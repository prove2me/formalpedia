-- Prove2me | Theorems.Thm_DRJointCC_Joint_theorem_3_3
-- name    : DRJointCC.Joint.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:17.810922+00:00
-- url     : https://prove2.me/theorems/13e8b8ff-5183-4d60-a22e-690be3034e10
-- title:
--   Theorem 3.3, p. 16 — Z^JCC(α) is the set of x admitting (β, M) with β + (1/ε)⟨Ω, M⟩ ≤ 0, M ≽ 0 and m LMIs (30)
-- statement:
--   Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma\succ0$, $\Omega$ its second-order moment matrix, $\epsilon\in(0,1)$, and consider a joint chance constraint with $m\ge1$ affine constraint functions $y_i^0(x)+y_i(x)^\top\xi$. For every vector $\alpha$ of strictly positive scaling parameters,
--   $$
--   \mathcal Z^{\mathrm{JCC}}(\alpha)=\left\{x\in\mathbb R^n:\ \begin{array}{l}\exists(\beta,M)\in\mathbb R\times\mathbb S^{k+1},\\ \beta+\frac1\epsilon\langle\Omega,M\rangle\le0,\quad M\succeq0,\\ M-\begin{bmatrix}0&\tfrac12\alpha_i y_i(x)\\ \tfrac12\alpha_i y_i(x)^\top&\alpha_i y_i^0(x)-\beta\end{bmatrix}\succeq0\quad\forall i=1,\dots,m\end{array}\right\}.
--   $$
--
--   The worst-case CVaR approximation of the joint chance constraint for fixed scaling parameters thus has an exact representation by linear matrix inequalities in $(x,\beta,M)$; the same $(\beta,M)$ serves all $m$ constraints.
--
--   **Formalization Note** The printed lower-left block reads "$\tfrac12\alpha_i y_i^\top$" without the argument $(x)$; it is the transpose of the upper-right block, and the formalization builds the symmetric block from $y_i(x)$. The equality is of sets: membership requires a feasible $(\beta,M)$ attaining value at most $0$, as printed. $m\ge1$, $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 16, Theorem 3.3, (30)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- Theorem 3.3, p. 16, (30): for `α ∈ 𝒜`, `x ∈ Z^JCC(α)` iff there are `β ∈ ℝ` and
`M ∈ 𝕊^{k+1}` with `β + (1/ε)⟨Ω, M⟩ ≤ 0`, `M ≽ 0` and
`M − [[0, ½α_i y_i(x)], [½α_i y_i(x)ᵀ, α_i y_i^0(x) − β]] ≽ 0` for every `i`. -/
theorem theorem_3_3 {m n k : ℕ} (hm : 0 < m) (D : JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    ZJCCα D μ Sig ε α =
      {x | ∃ (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ),
        β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧ M.PosSemidef ∧
          ∀ i, (M - lmiBlock D x α β i).PosSemidef} := by sorry

end DRJointCC.Joint
