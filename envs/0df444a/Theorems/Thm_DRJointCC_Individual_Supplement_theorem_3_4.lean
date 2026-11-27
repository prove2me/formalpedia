-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_3_4
-- name    : DRJointCC.Individual.Supplement.theorem_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:33:49.75283+00:00
-- url     : https://prove2.me/theorems/34e07438-c1ca-40a6-9b13-1ef608dee2ae
-- title:
--   Theorem 3.4, p. 19 — LMI representation of the quadratic-majorant approximation $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Consider the joint chance constraint with rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$, $i=1,\dots,m$, scaling parameters $\alpha\in\mathcal A=\{\alpha\in\mathbb R^m:\alpha>0\}$, and the quadratic-majorant approximation $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)$ of (38). Then $\mathcal Z_Q^{\mathrm{JCC}}(\alpha)$ is the set of $x\in\mathbb R^n$ for which there are $Q\in\mathbb S^k$, $q\in\mathbb R^k$, $q^0\in\mathbb R$, $\beta\in\mathbb R$ and $M\in\mathbb S^{k+1}$ with
--
--   $$
--   \beta+\tfrac1\epsilon\langle\Omega,M\rangle\le0,\qquad M\succeq0,\qquad M-\begin{bmatrix}Q&\frac12q\\\frac12q^\top&q^0-\beta\end{bmatrix}\succeq0,
--   $$
--
--   $$
--   \begin{bmatrix}Q&\frac12\big(q-\alpha_iy_i(x)\big)\\\frac12\big(q-\alpha_iy_i(x)\big)^\top&q^0-\alpha_iy_i^0(x)\end{bmatrix}\succeq0\qquad\forall i=1,\dots,m.
--   $$
--
--   Both inclusions are asserted. The first three constraints represent the robust quadratic chance constraint (37), the last $m$ the majorization (36).
--
--   Differences from the source:
--   - reading: "For any fixed x ∈ ℝ^n and α ∈ 𝒜 we have 𝒵_Q^JCC(α) = {x ∈ ℝ^n : …}" → for every α ∈ 𝒜, an equality of sets of x; reason: x is the bound variable of both sets; the "fixed x" in the hypothesis is a slip
--   - generalization: m ≥ 1 rows (a max over i = 1..m is taken in (36)) → no hypothesis on m; reason: 𝒵_Q^JCC(α) is defined through the row-by-row form of (36), which is meaningful for every m; the source's case m ≥ 1 is included
--   - encoding: inf_P P(q(ξ̃) ≤ 0) ≥ 1 − ε → ENNReal.ofReal (1 − ε) ≤ ⨅ P ∈ 𝒫, P{q ≤ 0} in ℝ≥0∞; reason: Lean convention; same instances
--   - encoding: M ∈ 𝕊^{k+1}, M ≽ 0, blocks indexed 1..k+1 → Matrix.PosSemidef (which includes symmetry) on Fin k ⊕ Unit with the extra index last; reason: Lean convention; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 19, Theorem 3.4 (with (36)–(38), p. 18)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_Majorant

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 3.4, p. 19: for `α ∈ 𝒜`, `x ∈ 𝒵_Q^JCC(α)` iff there are `Q ∈ 𝕊^k`, `q ∈ ℝ^k`,
`q⁰ ∈ ℝ`, `β ∈ ℝ`, `M ∈ 𝕊^{k+1}` with `β + (1/ε)⟨Ω, M⟩ ≤ 0`, `M ≽ 0`,
`M − [[Q, ½q], [½qᵀ, q⁰ − β]] ≽ 0` and
`[[Q, ½(q − α_i y_i(x))], [½(q − α_i y_i(x))ᵀ, q⁰ − α_i y_i⁰(x)]] ≽ 0` for every `i`. -/
theorem theorem_3_4 {m n k : ℕ} (D : DRJointCC.Joint.JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    ZQ D μ Sig ε α =
      {x | ∃ (Q : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) (q0 β : ℝ)
          (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
        Q.IsSymm ∧
          β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
          M.PosSemidef ∧
          (M - ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β)).PosSemidef ∧
          ∀ i, (ConvexOptimization.symQuadBlock Q
            ((1 / 2 : ℝ) • (q - α i • DRJointCC.Joint.y D i x))
            (q0 - α i * DRJointCC.Joint.y0 D i x)).PosSemidef} := by sorry

end DRJointCC.Individual.Supplement
