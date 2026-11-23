-- Prove2me | Theorems.Thm_DedekindZeta_normAtPlace_inv
-- name    : DedekindZeta.normAtPlace_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:41.782164+00:00
-- url     : https://prove2.me/theorems/2e828fbf-7040-4de7-afd9-38ed5f334a99
-- title:
--   Dedekind Zeta: norm At Place inv
-- statement:
--   The componentwise inversion of `K_ℝ` negates each place-norm exponent:
--   `normAtPlace w (x⁻¹) = (normAtPlace w x)⁻¹`. (The `Inv` on the mixed space is the
--   componentwise inverse of the real/complex coordinates.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L626-L632
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L626-L632

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.normAtPlace_inv (w : InfinitePlace K) (x : mixedEmbedding.mixedSpace K) :
    normAtPlace w x⁻¹ = (normAtPlace w x)⁻¹ := by sorry
