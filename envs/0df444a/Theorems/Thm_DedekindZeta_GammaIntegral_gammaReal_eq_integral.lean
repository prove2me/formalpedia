-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_gammaReal_eq_integral
-- name    : DedekindZeta.GammaIntegral.gammaReal_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:31.951802+00:00
-- url     : https://prove2.me/theorems/c22e016b-5e44-4dcd-891a-2e6f59136ec1
-- title:
--   Gamma Integral: gamma Real eq integral
-- statement:
--   `gammaReal` is the additive-`volume` integral of `realFactor` (unfolding the
--   `withDensity` defining `gammaReal` via `integral_withDensity_eq_integral_toReal_smul`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L344-L353
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L344-L353

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.GammaIntegral.gammaReal_eq_integral (s : ℂ) :
    gammaReal s = ∫ t : ℝ, realFactor s t := by sorry
