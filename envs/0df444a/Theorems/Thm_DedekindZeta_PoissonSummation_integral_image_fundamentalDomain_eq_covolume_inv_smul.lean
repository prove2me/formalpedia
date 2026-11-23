-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_integral_image_fundamentalDomain_eq_covolume_inv_smul
-- name    : DedekindZeta.PoissonSummation.integral_image_fundamentalDomain_eq_covolume_inv_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:07:31.437838+00:00
-- url     : https://prove2.me/theorems/104f6d08-0eae-463e-b82c-820e4a964015
-- title:
--   Poisson Summation: integral image fundamental Domain eq covolume inv smul
-- statement:
--   **Step 2b: covolume change of variables.** Substituting `y = Φ x` with
--   `Φ = latticeEquivFun L b`, the `Φ '' D` integral of `g ∘ red` equals
--   `(covolume L)⁻¹` times the integral over `D` of `g ∘ red ∘ Φ`, by the covolume
--   Jacobian `latticeEquivFun_map_volume` (`Φ` scales volume by `(covolume L)⁻¹`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1101-L1128
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1101-L1128

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

theorem DedekindZeta.PoissonSummation.integral_image_fundamentalDomain_eq_covolume_inv_smul
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in (latticeEquivFun L b) '' D,
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by sorry
