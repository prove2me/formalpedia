-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_eq_exp_quadForm
-- name    : DedekindZeta.ConeRadialReduction.mixedGaussian_eq_exp_quadForm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:28:51.834472+00:00
-- url     : https://prove2.me/theorems/dfeb6210-9e37-41d5-b06c-787d3b292246
-- title:
--   Cone Radial Reduction: mixed Gaussian eq exp quad Form
-- statement:
--   `mixedGaussian K y = exp(-π · Q(y))` (definitional unfolding through
--   `mixedQuadForm`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1241-L1242
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1241-L1242

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

theorem DedekindZeta.ConeRadialReduction.mixedGaussian_eq_exp_quadForm (y : mixedSpace K) :
    Theta.mixedGaussian K y = Real.exp (-Real.pi * mixedQuadForm K y) := by sorry
