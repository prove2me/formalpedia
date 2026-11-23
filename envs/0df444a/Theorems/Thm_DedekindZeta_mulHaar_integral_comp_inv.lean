-- Prove2me | Theorems.Thm_DedekindZeta_mulHaar_integral_comp_inv
-- name    : DedekindZeta.mulHaar_integral_comp_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:13.779314+00:00
-- url     : https://prove2.me/theorems/9f82cde9-9218-4a08-8c63-34f60932db61
-- title:
--   Dedekind Zeta: mul Haar integral comp inv
-- statement:
--   **Mellin-principle substitution** (the standard treatment): the change of
--   variables `x ↦ x⁻¹` in the multiplicative Mellin integral over `K_ℝ^*` is
--   measure-preserving, hence `∫ g(x) d^*x = ∫ g(x⁻¹) d^*x`. (The standard
--   measurability hypothesis on the integrand is required for the Bochner
--   change-of-variables; the theta-kernel integrand it is applied to satisfies it.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1196-L1203
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L1196-L1203

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

theorem DedekindZeta.mulHaar_integral_comp_inv (g : mixedEmbedding.mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g x ∂(mixedMulHaar K) = ∫ x, g x⁻¹ ∂(mixedMulHaar K) := by sorry
