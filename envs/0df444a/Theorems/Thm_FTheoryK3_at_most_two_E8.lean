-- Prove2me | Theorems.Thm_FTheoryK3_at_most_two_E8
-- name    : FTheoryK3.at_most_two_E8
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T20:01:23.695746+00:00
-- url     : https://prove2.me/theorems/e0aa0159-0184-46f3-9b67-ac0cc040677c
-- title:
--   At most two $E_8$ points on an elliptic K3
-- statement:
--   Let $k$ be a field of characteristic zero and let $f, g \in k[X]$ satisfy the Calabi--Yau/K3 degree data $$\deg f \le 8,\qquad \deg g \le 12,\qquad \Delta = 4f^3 + 27g^2 \ne 0.$$ Call $t_0 \in k$ an $E_8$ point if $\operatorname{ord}_{t_0}(f) \ge 4$ and $\operatorname{ord}_{t_0}(g) = 5$. Then the set of $E_8$ points is finite, and $$\#\{\, t_0 \in k : t_0 \text{ is an } E_8 \text{ point} \,\} \le 2.$$
--
--   Each $E_8$ point forces the discriminant to vanish to order $10$ there, while the total available order is $\deg\Delta \le 24$; hence at most two such points occur. This is the geometric origin of the heterotic $E_8 \times E_8$ gauge symmetry: an elliptic K3 accommodates at most two type II\* fibres.
--
--   **Formalization Note.** The statement bundles finiteness of the $E_8$-point set with the cardinality bound, so it does not rely on the convention that the cardinality of an infinite set is $0$. The count is over the affine chart; see the mission's formalization-scope note.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number of an elliptic surface = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24 singular fibres). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras up to E8, and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3Core
open Polynomial
variable {k : Type*} [Field k] [CharZero k]

namespace FTheoryK3
theorem at_most_two_E8
    (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | IsE8Point f g t₀}.Finite ∧
    Nat.card {t₀ : k | IsE8Point f g t₀} ≤ 2 := by
  sorry
end FTheoryK3
