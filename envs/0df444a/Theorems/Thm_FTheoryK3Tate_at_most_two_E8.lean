-- Prove2me | Theorems.Thm_FTheoryK3Tate_at_most_two_E8
-- name    : FTheoryK3Tate.at_most_two_E8
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:00:58.039894+00:00
-- url     : https://prove2.me/theorems/022209b2-1d9b-4a0d-981f-f9f399c2cec3
-- title:
--   Corollary — at most two $E_8$ points ($f=0$-faithful)
-- statement:
--   Let $k$ be a field of characteristic zero and $(f,g)$ satisfy the K3 degree data. Then the set of $E_8$ points (type $\mathrm{II}^*$ fibres, `IsE8Point`) is finite and has at most two elements. The finiteness is asserted jointly with the cardinality bound, so it cannot be met vacuously via the convention that an infinite set has cardinality $0$. This restates the headline $E_8 \times E_8$ count on the $f = 0$-faithful `IsE8Point` (encoding $\operatorname{ord} f \ge 4$ as $(X - t_0)^4 \mid f$).
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Corollary (`E₈ × E₈` maximal enhancement). On a Calabi–Yau/K3 model there are only finitely
    many `E₈` (type II*) points, and at most two of them — since each contributes `10` to the
    discriminant budget and `3 × 10 = 30 > 24`. This restates the headline count on the
    `f = 0`-faithful `IsE8Point` (via `(X - C t₀)^4 ∣ f`), fixing the earlier
    `rootMultiplicity`-only encoding. -/
theorem at_most_two_E8 (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | IsE8Point f g t₀}.Finite ∧
    Nat.card {t₀ : k | IsE8Point f g t₀} ≤ 2 := by
  sorry
end FTheoryK3Tate
