-- Prove2me | Theorems.Thm_FTheoryK3_rootMultiplicity_discriminant_of_isE8Point
-- name    : FTheoryK3.rootMultiplicity_discriminant_of_isE8Point
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T20:00:27.754266+00:00
-- url     : https://prove2.me/theorems/40e97933-8366-46b0-b094-3438a46c35fe
-- title:
--   A type II\* ($E_8$) fibre has $\operatorname{ord}_{t_0}\Delta = 10$
-- statement:
--   Let $k$ be a field of characteristic zero and let $f, g \in k[X]$. Suppose $t_0 \in k$ is an $E_8$ (Kodaira type II\*) point, i.e. $$\operatorname{ord}_{t_0}(f) \ge 4 \qquad\text{and}\qquad \operatorname{ord}_{t_0}(g) = 5.$$ Then the discriminant $\Delta = 4f^3 + 27g^2$ vanishes at $t_0$ to order exactly $10$: $$\operatorname{ord}_{t_0}(\Delta) = 10.$$
--
--   This is the local fingerprint of a type II\* fibre: $\operatorname{ord}_{t_0}(4f^3) = 3\,\operatorname{ord}_{t_0}(f) \ge 12$ exceeds $\operatorname{ord}_{t_0}(27g^2) = 10$, so the discriminant inherits the smaller order. It is the per-brane multiplicity summed against the global bound.
--
--   **Formalization Note.** Characteristic zero guarantees $4$ and $27$ are nonzero in $k$. An order of exactly $10$ implies in particular that $\Delta \ne 0$.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number of an elliptic surface = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24 singular fibres). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras up to E8, and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3Core
open Polynomial
variable {k : Type*} [Field k] [CharZero k]

namespace FTheoryK3
theorem rootMultiplicity_discriminant_of_isE8Point
    (f g : k[X]) (t₀ : k) (h : IsE8Point f g t₀) :
    (Δ f g).rootMultiplicity t₀ = 10 := by
  sorry
end FTheoryK3
