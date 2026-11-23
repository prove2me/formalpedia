-- Prove2me | Theorems.Thm_DRJointCC_Individual_Supplement_theorem_2_1
-- name    : DRJointCC.Individual.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:30:36.0194+00:00
-- url     : https://prove2.me/theorems/1777948d-6fa1-4d75-ae22-a0ff50b5b470
-- title:
--   Theorem 2.1, p. 6 — LMI representation of the worst-case CVaR feasible set $\mathcal Z^{\mathrm{ICC}}$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Let $y^0:\mathbb R^n\to\mathbb R$ and $y:\mathbb R^n\to\mathbb R^k$, and let $\mathcal Z^{\mathrm{ICC}}=\{x:\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon(y^0(x)+y(x)^\top\tilde\xi)\le0\}$ be the worst-case CVaR feasible set (8). Then
--
--   $$
--   \mathcal Z^{\mathrm{ICC}}=\left\{x\in\mathbb R^n:\ \exists(\beta,M)\in\mathbb R\times\mathbb S^{k+1},\ M\succeq0,\ \beta+\tfrac1\epsilon\langle\Omega,M\rangle\le0,\ M-\begin{bmatrix}0&\frac12y(x)\\\frac12y(x)^\top&y^0(x)-\beta\end{bmatrix}\succeq0\right\}.
--   $$
--
--   Both inclusions are asserted. The theorem makes the conservative approximation $\mathcal Z^{\mathrm{ICC}}$ of the distributionally robust individual chance constraint tractable; by Theorem 2.2 it is in fact exact for this affine loss.
--
--   Differences from the source:
--   - generalization: y^0(x) = (a^0)ᵀx − b^0 and y(x) affine in x (p. 2) → arbitrary maps y0 : ℝ^n → ℝ and y : ℝ^n → ℝ^k; reason: the claim is pointwise in x, so it holds for any values y^0(x), y(x); the affine maps of the paper are a special case
--   - encoding: worst-case CVaR, a real number or +∞ → extended-real CVaR with E_P[(L − β)^+] a lower Lebesgue integral (published cvar / wcCVaR); reason: Lean convention; +∞ is represented instead of a junk value; same instances
--   - encoding: M ∈ 𝕊^{k+1}, M ≽ 0, blocks indexed 1..k+1 → Matrix.PosSemidef (which includes symmetry) on Fin k ⊕ Unit with the extra index last; reason: Lean convention; same instances
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 6, Theorem 2.1 (with (8))

import Mathlib
import Definitions.Def_DRJointCC_Individual_Supplement_ZICC

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- Theorem 2.1, p. 6: the worst-case CVaR feasible set `𝒵^ICC` of the individual chance
constraint is the set of `x` for which there are `β ∈ ℝ` and `M ∈ 𝕊^{k+1}` with `M ≽ 0`,
`β + (1/ε)⟨Ω, M⟩ ≤ 0` and `M − [[0, ½y(x)], [½y(x)ᵀ, y⁰(x) − β]] ≽ 0`. -/
theorem theorem_2_1 {n k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (y0 : (Fin n → ℝ) → ℝ) (y : (Fin n → ℝ) → Fin k → ℝ) :
    ZICC ε μ Sig y0 y =
      {x | ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
        M.PosSemidef ∧
          β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
          (M - ConvexOptimization.symQuadBlock 0 ((1 / 2 : ℝ) • y x) (y0 x - β)).PosSemidef} := by sorry

end DRJointCC.Individual.Supplement
