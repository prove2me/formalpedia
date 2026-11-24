-- Prove2me | Theorems.Thm_FTheoryK3Tate_discOrder_IV
-- name    : FTheoryK3Tate.discOrder_IV
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T08:57:20.326469+00:00
-- url     : https://prove2.me/theorems/901ddc07-4144-44d4-90ca-1f751e4a32f3
-- title:
--   Tate table: type IV has $\operatorname{ord}\Delta = 4$
-- statement:
--   Let $k$ be a field of characteristic zero and $f, g \in k[X]$. If the fibre at $t_0 \in k$ has Kodaira/Tate type $\mathrm{IV}$ — i.e. $\operatorname{ord} f \ge 2$ and $\operatorname{ord} g = 2$ — then the discriminant $\Delta = 4f^3 + 27g^2$ vanishes at $t_0$ to order exactly $4$: $\operatorname{ord}_{t_0}(\Delta) = 4$. This is the corresponding entry of the Tate table; in characteristic zero the constants $4, 27$ are units, so $\operatorname{ord}(4f^3) = 3\operatorname{ord} f$ and $\operatorname{ord}(27g^2) = 2\operatorname{ord} g$, and $\Delta$ inherits the smaller of the two orders when they differ.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Tate table, type **IV**: `ord f ≥ 2`, `ord g = 2` force `ord Δ = 4`.
    (Here `ord(27g²) = 4 < 6 ≤ ord(4f³)`.) -/
theorem discOrder_IV (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.IV) :
    (Δ f g).rootMultiplicity t₀ = 4 := by
  sorry
end FTheoryK3Tate
