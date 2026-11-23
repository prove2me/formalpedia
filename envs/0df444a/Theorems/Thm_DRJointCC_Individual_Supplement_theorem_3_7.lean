-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_3_7
-- name    : DRJointCC.Individual.Supplement.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:35:01.664071+00:00
-- url     : https://prove2.me/theorems/35e183e1-4eba-47ec-a756-f113d5dfde1a
-- title:
--   Theorem 3.7, p. 23 — with support information, 𝒴_Ξ^JCC(α) ⊆ 𝒵_Ξ^JCC(α) ⊆ 𝒳_Ξ^JCC, with 𝒴 = 𝒵 for one quadratic support constraint (l = 1)
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Let $W_1,\dots,W_l\in\mathbb S^{k+1}$, $\Xi=\{\xi:[\xi^\top\ 1]W_j[\xi^\top\ 1]^\top\le0,\ j=1,\dots,l\}$, and let $\mathcal P_\Xi$ be the distributions with mean $\mu$ and covariance $\Sigma$ supported on $\Xi$. Assume, as in §3.6, that the true distribution $\mathbb Q$ belongs to $\mathcal P_\Xi$; in particular $\mathcal P_\Xi\neq\emptyset$. Consider the joint chance constraint with $m\ge1$ rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$ and the sets $\mathcal X_\Xi^{\mathrm{JCC}}$, $\mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)$ and $\mathcal Y_\Xi^{\mathrm{JCC}}(\alpha)$ of pp. 22–23. Then for every $\alpha\in\mathcal A=\{\alpha>0\}$:
--
--   1. $\mathcal Y_\Xi^{\mathrm{JCC}}(\alpha)\subseteq\mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)$;
--   2. $\mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)\subseteq\mathcal X_\Xi^{\mathrm{JCC}}$;
--   3. if $l=1$, then $\mathcal Y_\Xi^{\mathrm{JCC}}(\alpha)=\mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)$.
--
--   The LMI set (43) is thus a tractable conservative approximation of the support-constrained joint chance constraint, and it is exact relative to the worst-case CVaR approximation when the support is described by a single quadratic inequality.
--
--   Differences from the source:
--   - encoding: ℚ, with mean μ and covariance Σ ≻ 0, is supported on Ξ → hypothesis that 𝒫_Ξ is nonempty; reason: only ℚ's membership in 𝒫_Ξ enters the statement; the two are the same assumption
--   - encoding: ℙ supported on Ξ → ℙ(Ξᶜ) = 0; reason: definition of support used on p. 22 (ℚ(ξ̃ ∈ Ξ) = 1)
--   - encoding: τ_0, …, τ_m ∈ ℝ^l → τ0 : Fin l → ℝ and τ : Fin m → Fin l → ℝ (τ i is τ_{i+1}); reason: 0-based indexing; same instances
--   - encoding: max_{i=1,…,m} with m ≥ 1 implicit → ⨆ over Fin m with the hypothesis 0 < m; reason: the max is the finite supremum for m ≥ 1; standing convention of the published 02 items
--   - encoding: worst-case CVaR, a real number or +∞ → extended-real CVaR with E_P[(L − β)^+] a lower Lebesgue integral (published cvar / wcCVaR); reason: Lean convention; +∞ is represented instead of a junk value; same instances
--   - encoding: M ∈ 𝕊^{k+1}, M ≽ 0, blocks indexed 1..k+1 → Matrix.PosSemidef (which includes symmetry) on Fin k ⊕ Unit with the extra index last; reason: Lean convention; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 23, Theorem 3.7 and (43); p. 22, §3.6 Distributional Assumptions, X_Ξ^JCC, Z_Ξ^JCC(α)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Support

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 3.7, p. 23: with support information `Ξ = {ξ : [ξᵀ 1] W_j [ξᵀ 1]ᵀ ≤ 0, j ≤ l}`
(`W_j ∈ 𝕊^{k+1}`) and a distribution with mean `μ`, covariance `Σ ≻ 0` supported on `Ξ`
(so `𝒫_Ξ ≠ ∅`), for every `α ∈ 𝒜`: `𝒴_Ξ^JCC(α) ⊆ 𝒵_Ξ^JCC(α) ⊆ 𝒳_Ξ^JCC`, and for `l = 1`,
`𝒴_Ξ^JCC(α) = 𝒵_Ξ^JCC(α)`. -/
theorem theorem_3_7 {m n k l : ℕ} (hm : 0 < m) (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (hW : ∀ j, (W j).IsHermitian)
    (hsupp : (PXi μ Sig W).Nonempty)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    YXi D μ Sig ε W α ⊆ ZXi D μ Sig ε W α ∧
      ZXi D μ Sig ε W α ⊆ XXi D μ Sig ε W ∧
      (l = 1 → YXi D μ Sig ε W α = ZXi D μ Sig ε W α) := by sorry

end DRJointCC.Individual.Supplement
