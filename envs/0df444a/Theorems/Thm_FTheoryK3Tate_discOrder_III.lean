-- Prove2me | Theorems.Thm_FTheoryK3Tate_discOrder_III
-- name    : FTheoryK3Tate.discOrder_III
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T08:56:48.913552+00:00
-- url     : https://prove2.me/theorems/1117f586-ceaf-40e1-bb5a-80501fb376f5
-- title:
--   Tate table: type III has $\operatorname{ord}\Delta = 3$
-- statement:
--   Let $k$ be a field of characteristic zero and $f, g \in k[X]$. If the fibre at $t_0 \in k$ has Kodaira/Tate type $\mathrm{III}$ — i.e. $\operatorname{ord} f = 1$ and $\operatorname{ord} g \ge 2$ — then the discriminant $\Delta = 4f^3 + 27g^2$ vanishes at $t_0$ to order exactly $3$: $\operatorname{ord}_{t_0}(\Delta) = 3$. This is the corresponding entry of the Tate table; in characteristic zero the constants $4, 27$ are units, so $\operatorname{ord}(4f^3) = 3\operatorname{ord} f$ and $\operatorname{ord}(27g^2) = 2\operatorname{ord} g$, and $\Delta$ inherits the smaller of the two orders when they differ.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Tate table, type **III**: `ord f = 1`, `ord g ≥ 2` force `ord Δ = 3`.
    (Here `ord(4f³) = 3 < 4 ≤ ord(27g²)`.) -/
theorem discOrder_III (f g : k[X]) (t₀ : k) (h : HasKodaira f g t₀ Kodaira.III) :
    (Δ f g).rootMultiplicity t₀ = 3 := by
  sorry
end FTheoryK3Tate
