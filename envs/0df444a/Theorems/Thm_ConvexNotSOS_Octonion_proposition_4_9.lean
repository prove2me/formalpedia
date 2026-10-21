-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_proposition_4_9
-- name    : ConvexNotSOS.Octonion.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:35.723353+00:00
-- url     : https://prove2.me/theorems/e764e001-bfca-4521-a65b-59b979357728
-- title:
--   Proposition 4.9 — invariant quartic SOS feasibility
-- statement:
--   Let $k\ge2$, and let $f$ be a quartic form in $16k$ real variables invariant under $X\mapsto gXh^\top$ for $g\in\operatorname{Spin}(9)$ and $h\in O(k)$. Then $f$ is SOS exactly when nonnegative coefficients $\lambda_{ij}$ exist, indexed by the eight pairs in $\Lambda$, such that
--
--   $$f(X)=\sum_{(i,j)\in\Lambda}\lambda_{ij}s_{ij}(X)\qquad\text{for every }X\in\mathbb R^{16\times k}.$$
--
--   This reduces an invariant SOS problem to a finite cone of eight explicit quartic forms.
--
--   **Formalization Note.** The source's standing representation-theory regime is $k\ge2$; Proposition 4.10 is false at $k=1$. The group is the paper's concrete matrix model $G$, and the $s_{ij}$ are the equivalent projection forms defined in the Symmetry item.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 13, Proposition 4.9

import Definitions.Def_ConvexNotSOS_Octonion_Symmetry

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem proposition_4_9 (k : ℕ) (hk : 2 ≤ k)
    (f : MvPolynomial (Var k) ℝ) (hf : f.IsHomogeneous 4)
    (hinv : ∀ g ∈ spin9, ∀ h ∈ Matrix.orthogonalGroup (Fin k) ℝ,
      ∀ X : Matrix (Fin 16) (Fin k) ℝ,
        evalM (g * X * h.transpose) f = evalM X f) :
    IsSumSq f ↔ ∃ coeff : Lam → ℝ, (∀ l, 0 ≤ coeff l) ∧
      ∀ X : Matrix (Fin 16) (Fin k) ℝ,
        evalM X f = ∑ l : Lam, coeff l * evalM X (sPoly k l) := by sorry
end ConvexNotSOS.Octonion
