-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mapsTo_radialMap_closure_normEqOneSurface
-- name    : DedekindZeta.ConeRadialReduction.mapsTo_radialMap_closure_normEqOneSurface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:49:10.684347+00:00
-- url     : https://prove2.me/theorems/920a0462-5240-4f57-8daf-21acb555c4ec
-- title:
--   Cone Radial Reduction: maps To radial Map closure norm Eq One Surface
-- statement:
--   For `r > 0`, the radial scaling `radialMap K r` maps the closure of the
--   norm-1 surface into the nonzero-norm locus: for `x` with `N x = 1` we get
--   `N (radialMap K r x) = r > 0` (`norm_radialMap`).  the standard treatment.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1600-L1606
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1600-L1606

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem DedekindZeta.ConeRadialReduction.mapsTo_radialMap_closure_normEqOneSurface (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (radialMap K r) (closure (normEqOneSurface K))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by sorry
