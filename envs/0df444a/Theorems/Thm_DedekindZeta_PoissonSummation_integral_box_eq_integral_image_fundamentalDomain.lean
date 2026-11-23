-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_integral_box_eq_integral_image_fundamentalDomain
-- name    : DedekindZeta.PoissonSummation.integral_box_eq_integral_image_fundamentalDomain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:07:03.022672+00:00
-- url     : https://prove2.me/theorems/2c474e65-524a-4ab1-9801-c762cbcc42db
-- title:
--   Poisson Summation: integral box eq integral image fundamental Domain
-- statement:
--   **Step 2a: periodic fundamental-domain swap.** The half-open box
--   `(Ioc 0 1)^d` and `Φ '' D` (with `Φ = latticeEquivFun L b`) are both fundamental
--   domains of the integer lattice `ℤ^d` (the latter by `latticeEquivFun_image_lattice`),
--   and the integrand `g ∘ red` is `ℤ^d`-periodic (`red` collapses integer
--   translations), so the box and `Φ '' D` integrals agree.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L988-L1095
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L988-L1095

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

theorem DedekindZeta.PoissonSummation.integral_box_eq_integral_image_fundamentalDomain
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = ∫ y in (latticeEquivFun L b) '' D,
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by sorry
