-- Prove2me | Theorems.Thm_DRJointCC_Joint_eq_40
-- name    : DRJointCC.Joint.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:11.036953+00:00
-- url     : https://prove2.me/theorems/a44c882d-7856-4feb-b1f1-bf47e4d8845e
-- title:
--   (40), p. 21 — X°^JCC is the set of x admitting M ≽ 0 and α > 0 with ⟨Ω, M⟩ ≤ ε and m LMIs
-- statement:
--   Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma\succ0$, $\Omega$ its second-order moment matrix, $\epsilon\in(0,1)$, and consider a joint chance constraint with $m\ge1$ affine constraint functions $y_i^0(x)+y_i(x)^\top\xi$. The strict robust joint chance constraint set has the representation
--   $$
--   \mathcal X^{\mathrm{JCC}}_\circ=\left\{x\in\mathbb R^n:\ \begin{array}{l}\exists M\in\mathbb S^{k+1},\ \alpha\in\mathbb R^m,\\ \langle\Omega,M\rangle\le\epsilon,\quad M\succeq0,\quad\alpha>0,\\ M-\begin{bmatrix}0&\tfrac12\alpha_i y_i(x)\\ \tfrac12\alpha_i y_i(x)^\top&\alpha_i y_i^0(x)+1\end{bmatrix}\succeq0\quad\forall i=1,\dots,m\end{array}\right\}.
--   $$
--
--   The multipliers $\alpha$ produced here play the role of the scaling parameters of the worst-case CVaR approximation, which is how the strict set is compared with $\mathcal Z^{\mathrm{JCC}}$ in Theorem 3.6.
--
--   **Formalization Note** $\alpha>0$ is componentwise strict positivity, as printed (the page notes that no feasible $\alpha$ has a vanishing component). The LMI block equals the block of Theorem 3.3 with $\beta=-1$. $m\ge1$, $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses. No nondegeneracy assumption on the constraint functions is made.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 21, proof of Theorem 3.6, (40)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- (40), p. 21: `x ∈ X°^JCC` iff there are `M ∈ 𝕊^{k+1}` and `α ∈ ℝ^m` with
`⟨Ω, M⟩ ≤ ε`, `M ≽ 0`, `α > 0` componentwise and
`M − [[0, ½α_i y_i(x)], [½α_i y_i(x)ᵀ, α_i y_i^0(x) + 1]] ≽ 0` for every `i`. -/
theorem eq_40 {m n k : ℕ} (hm : 0 < m) (D : JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    XJCCStrict D μ Sig ε =
      {x | ∃ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (α : Fin m → ℝ),
        DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ ε ∧ M.PosSemidef ∧ (∀ i, 0 < α i) ∧
          ∀ i, (M - ConvexOptimization.symQuadBlock 0 ((α i / 2) • y D i x)
            (α i * y0 D i x + 1)).PosSemidef} := by sorry

end DRJointCC.Joint
