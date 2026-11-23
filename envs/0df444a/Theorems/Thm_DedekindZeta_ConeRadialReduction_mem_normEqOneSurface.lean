-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
-- name    : DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:23.7282+00:00
-- url     : https://prove2.me/theorems/e579d975-1dfc-470a-93ed-4aa0d1ab405a
-- title:
--   Cone Radial Reduction: mem norm Eq One Surface
-- statement:
--   The Cone Radial Reduction construction uses the mem norm Eq One Surface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L81-L84
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L81-L84

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

theorem DedekindZeta.ConeRadialReduction.mem_normEqOneSurface {x : mixedSpace K} :
    x ∈ normEqOneSurface K ↔
      x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x = 1 := by sorry
