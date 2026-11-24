-- Prove2me | Theorems.Thm_FTheoryK3_discriminant_natDegree_le
-- name    : FTheoryK3.discriminant_natDegree_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T19:59:54.425592+00:00
-- url     : https://prove2.me/theorems/f93e5d16-77a8-4e84-b3d5-f3dfb7f8665e
-- title:
--   24 seven-branes: $\deg\Delta \le 24$
-- statement:
--   Let $k$ be a field and let $f, g \in k[X]$ be the coefficients of the Weierstrass model $y^2 = x^3 + f\,x + g$. If $$\deg f \le 8 \qquad\text{and}\qquad \deg g \le 12,$$ then the discriminant $\Delta = 4f^3 + 27g^2$ satisfies $$\deg \Delta \le 24.$$
--
--   In F-theory language these degree bounds are the Calabi--Yau condition for an elliptic fibration over $\mathbb{P}^1$, and $\deg\Delta = 24$ counts the 7-branes (equal to $\chi(\mathrm{K3})$). The bound $\deg\Delta \le 24$ is the algebraic content of that count; the extremal value is attained in the generic K3 case.
--
--   **Formalization Note.** Degrees use `natDegree`, so the zero polynomial has degree $0$ and the inequality holds trivially if $\Delta = 0$.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number of an elliptic surface = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24 singular fibres). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras up to E8, and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3Core
open Polynomial
variable {k : Type*} [Field k]

namespace FTheoryK3
theorem discriminant_natDegree_le
    (f g : k[X]) (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (Δ f g).natDegree ≤ 24 := by
  sorry
end FTheoryK3
