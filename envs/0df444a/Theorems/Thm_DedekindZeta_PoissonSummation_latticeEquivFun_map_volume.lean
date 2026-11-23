-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_latticeEquivFun_map_volume
-- name    : DedekindZeta.PoissonSummation.latticeEquivFun_map_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:51:33.608794+00:00
-- url     : https://prove2.me/theorems/339066c9-a076-4342-917a-5839e3712088
-- title:
--   Poisson Summation: lattice Equiv Fun map volume
-- statement:
--   **Step 2: unit box = covolume⁻¹ • fundamental-domain integral.** Substitute
--   `y = Φ x` with `Φ = latticeEquivFun L b`: `Φ` carries the fundamental domain `D`
--   onto a fundamental box of `ℤ^d` (same product torus image as the standard
--   `(Ioc 0 1)^d` box, by `latticeEquivFun_image_lattice`), and scales Lebesgue
--   volume by `(covolume L)⁻¹` (`ZLattice.volume_image_eq_volume_div_covolume`).
--   Hence the box integral of `g ∘ red` equals `(covolume L)⁻¹` times the integral
--   over `D` of `g ∘ red ∘ Φ`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L955-L981
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L955-L981

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)

theorem DedekindZeta.PoissonSummation.latticeEquivFun_map_volume :
    Measure.map (latticeEquivFun L b) volume
      = ENNReal.ofReal (ZLattice.covolume L) • (volume : Measure (Fin d → ℝ)) := by sorry
