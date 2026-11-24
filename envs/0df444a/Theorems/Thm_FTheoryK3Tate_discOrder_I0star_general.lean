-- Prove2me | Theorems.Thm_FTheoryK3Tate_discOrder_I0star_general
-- name    : FTheoryK3Tate.discOrder_I0star_general
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:56:08.80043+00:00
-- url     : https://prove2.me/theorems/0567203e-8e61-4949-8cb5-410d665e3f9c
-- title:
--   discOrder_I0star_general
-- statement:
--   The full type $\mathrm{I}_0^*$ row. If $\operatorname{ord}_t f \ge 2$, $\operatorname{ord}_t g \ge 3$, and the reduced discriminant $4c_2^3 + 27 d_3^2 \ne 0$ (where $c_2,d_3$ are the leading local Taylor coefficients of $f,g$ at $t$, i.e. the coefficients of $(X-t)^2$ in $f$ and $(X-t)^3$ in $g$), then the discriminant $\Delta = 4f^3+27g^2$ satisfies $\operatorname{ord}_t\Delta = 6$. This covers all three $\mathrm{I}_0^*$ branches; the nonvanishing reduced discriminant is the distinct-roots criterion separating $\mathrm{I}_0^*$ from the $\mathrm{I}_n^*$ series. No characteristic hypothesis is required.
-- source:
--   Kodaira/Tate classification of singular fibres: J. Tate (LNM 476, 1975); M. Schuett, T. Shioda, Elliptic Surfaces, arXiv:0907.0298; F-theory dictionary: T. Weigand, TASI Lectures on F-theory, arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k]
/-- The full type **I₀\*** row (all branches). At a point with `ord f ≥ 2`, `ord g ≥ 3`, and
    nonzero reduced discriminant `4 c₂³ + 27 d₃² ≠ 0` — where `c₂ = (taylor t₀ f).coeff 2` and
    `d₃ = (taylor t₀ g).coeff 3` are the leading local coefficients — the discriminant vanishes to
    order exactly `6`. This covers all three I₀* cases (`ord f = 2, ord g = 3`; `ord f = 2, ord g > 3`;
    `ord f > 2, ord g = 3`); the `≠ 0` condition is the distinct-roots criterion for the cubic
    `x³ + c₂ x + d₃`, which is exactly what separates I₀* from the potentially multiplicative
    `Iₙ*` series. No characteristic hypothesis is needed: the order-6 coefficient of `Δ` is
    literally `4 c₂³ + 27 d₃²`. -/
theorem discOrder_I0star_general (f g : k[X]) (t₀ : k)
    (hf : (X - C t₀) ^ 2 ∣ f) (hg : (X - C t₀) ^ 3 ∣ g)
    (hred : 4 * ((taylor t₀ f).coeff 2) ^ 3 + 27 * ((taylor t₀ g).coeff 3) ^ 2 ≠ 0) :
    (Δ f g).rootMultiplicity t₀ = 6 := by
  sorry
end FTheoryK3Tate
