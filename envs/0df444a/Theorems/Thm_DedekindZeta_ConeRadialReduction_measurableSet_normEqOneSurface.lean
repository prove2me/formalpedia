-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
-- name    : DedekindZeta.ConeRadialReduction.measurableSet_normEqOneSurface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:53.822684+00:00
-- url     : https://prove2.me/theorems/cf3c7db9-5c36-42a2-9cf4-3e324749df20
-- title:
--   Cone Radial Reduction: measurable Set norm Eq One Surface
-- statement:
--   The Cone Radial Reduction construction uses the measurable Set norm Eq One Surface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L86-L89
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L86-L89

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

theorem DedekindZeta.ConeRadialReduction.measurableSet_normEqOneSurface :
    MeasurableSet (normEqOneSurface K) := by sorry
