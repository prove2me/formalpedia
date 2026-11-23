-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_2_3
-- name    : DRJointCC.Individual.Supplement.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:32:36.356598+00:00
-- url     : https://prove2.me/theorems/d50cc3e1-24b8-4ba3-8ab7-55da3b229484
-- title:
--   Theorem 2.3, p. 11 — for piecewise affine concave or quadratic L, the worst-case CVaR equals the value of SDP (23), resp. the SDP after (25)
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   1. **Piecewise affine concave loss.** Let $l\ge1$, $a_1,\dots,a_l\in\mathbb R$, $b_1,\dots,b_l\in\mathbb R^k$, and $L(\xi)=\min_{i=1,\dots,l}\{a_i+b_i^\top\xi\}$. Write $\Delta=\{\lambda\in\mathbb R^l:\sum_i\lambda_i=1,\ \lambda\ge0\}$. Then
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(L(\tilde\xi)\big)=\inf\Big\{\beta+\tfrac1\epsilon\langle\Omega,M\rangle:\ \beta\in\mathbb R,\ M\in\mathbb S^{k+1},\ \lambda\in\Delta,\ M\succeq0,\ M-\begin{bmatrix}0&\sum_{i}\frac{\lambda_i}2b_i\\\sum_i\frac{\lambda_i}2b_i^\top&\sum_i\lambda_ia_i-\beta\end{bmatrix}\succeq0\Big\}. \tag{23}
--   $$
--
--   2. **Quadratic loss.** Let $Q\in\mathbb S^k$, $q\in\mathbb R^k$, $q^0\in\mathbb R$ and $L(\xi)=\xi^\top Q\xi+q^\top\xi+q^0$ (not necessarily convex or concave). Then
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(L(\tilde\xi)\big)=\inf\Big\{\beta+\tfrac1\epsilon\langle\Omega,M\rangle:\ M\in\mathbb S^{k+1},\ \beta\in\mathbb R,\ M\succeq0,\ M-\begin{bmatrix}Q&\frac12q\\\frac12q^\top&q^0-\beta\end{bmatrix}\succeq0\Big\}.
--   $$
--
--   The infima are optimal values of semidefinite programs, so the worst-case CVaR of these two loss classes can be computed by semidefinite programming. Case 2 is the representation used for the quadratic chance constraint (37) in Theorem 3.4.
--
--   Differences from the source:
--   - reading: sup_P P-CVaR_ε(L(ξ̃)) "can be computed efficiently as the optimal value of a tractable SDP" → sup_P P-CVaR_ε(L) equals the optimal value of SDP (23) in case (i) and of the SDP after (25) in case (ii); reason: the proof identifies these SDPs as the claimed ones; "efficiently" and "tractable" refer to the solvability of SDPs and carry no further formal content
--   - reading: L concave piecewise affine in ξ with a finite number of pieces → L(ξ) = min_{i=1..l} {a_i + b_iᵀξ} with l ≥ 1; reason: the proof starts from this form; a concave piecewise affine function with finitely many pieces is the minimum of its pieces, and l ≥ 1 because a function has at least one piece
--   - encoding: optimal value of an SDP → extended-real infimum over the feasible set (+∞ if infeasible); reason: Lean convention; no junk real infimum
--   - encoding: worst-case CVaR, a real number or +∞ → extended-real CVaR with E_P[(L − β)^+] a lower Lebesgue integral (published cvar / wcCVaR); reason: Lean convention; +∞ is represented instead of a junk value; same instances
--   - encoding: M ∈ 𝕊^{k+1}, M ≽ 0, blocks indexed 1..k+1 → Matrix.PosSemidef (which includes symmetry) on Fin k ⊕ Unit with the extra index last; reason: Lean convention; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 11, Theorem 2.3, with its proof pp. 11–13 ((21)–(25), SDP (23) and the SDP after (25))

import Mathlib
import Definitions.Def_DRJointCC_Individual_Moments

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 2.3, p. 11, with the SDPs given in its proof (pp. 12–13).
(i) For a concave piecewise affine loss `L(ξ) = min_{i=1,…,l} {a_i + b_iᵀξ}` (`l ≥ 1`), the
worst-case CVaR `sup_{ℙ ∈ 𝒫} ℙ-CVaR_ε(L(ξ̃))` equals the optimal value of SDP (23):
`inf β + (1/ε)⟨Ω, M⟩` over `β ∈ ℝ`, `M ∈ 𝕊^{k+1}`, `λ ∈ ℝ^l` with `M ≽ 0`, `λ ∈ Δ` and
`M − [[0, Σ_i (λ_i/2) b_i], [Σ_i (λ_i/2) b_iᵀ, Σ_i λ_i a_i − β]] ≽ 0`.
(ii) For a quadratic loss `L(ξ) = ξᵀQξ + qᵀξ + q⁰` with `Q ∈ 𝕊^k`, it equals the optimal value
of the SDP following (25): `inf β + (1/ε)⟨Ω, M⟩` over `M ≽ 0`, `β ∈ ℝ` with
`M − [[Q, ½q], [½qᵀ, q⁰ − β]] ≽ 0`.
Both optimal values are extended-real infima (`+∞` when infeasible). -/
theorem theorem_2_3 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∀ (l : ℕ), 0 < l → ∀ (a : Fin l → ℝ) (b : Fin l → Fin k → ℝ),
      DRJointCC.Individual.wcCVaR ε μ Sig (fun ξ => ⨅ i : Fin l, (a i + b i ⬝ᵥ ξ)) =
        ⨅ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (lam : Fin l → ℝ)
          (_ : M.PosSemidef ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
            (M - ConvexOptimization.symQuadBlock 0 (∑ i, (lam i / 2) • b i)
              (∑ i, lam i * a i - β)).PosSemidef),
          ((β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M : ℝ) :
            EReal)) ∧
    (∀ (Q : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) (q0 : ℝ), Q.IsSymm →
      DRJointCC.Individual.wcCVaR ε μ Sig (fun ξ => ξ ⬝ᵥ Q.mulVec ξ + q ⬝ᵥ ξ + q0) =
        ⨅ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
          (_ : M.PosSemidef ∧
            (M - ConvexOptimization.symQuadBlock Q ((1 / 2 : ℝ) • q) (q0 - β)).PosSemidef),
          ((β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M : ℝ) :
            EReal)) := by sorry

end DRJointCC.Individual.Supplement
