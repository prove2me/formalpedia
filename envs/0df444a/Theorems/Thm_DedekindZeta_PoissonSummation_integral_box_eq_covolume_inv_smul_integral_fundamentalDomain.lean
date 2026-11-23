-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_integral_box_eq_covolume_inv_smul_integral_fundamentalDomain
-- name    : DedekindZeta.PoissonSummation.integral_box_eq_covolume_inv_smul_integral_fundamentalDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:07:08.148144+00:00
-- url     : https://prove2.me/theorems/d182b940-f37a-4353-8ab7-a44ce21443ba
-- title:
--   Poisson Summation: integral box eq covolume inv smul integral fundamental Domain
-- statement:
--   The Poisson Summation construction uses the integral box eq covolume inv smul integral fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1130-L1138
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1130-L1138

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

theorem DedekindZeta.PoissonSummation.integral_box_eq_covolume_inv_smul_integral_fundamentalDomain
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by sorry
