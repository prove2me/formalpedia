-- Prove2me | Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
-- name    : DedekindZeta.mixedEmbedding_norm_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:03.269115+00:00
-- url     : https://prove2.me/theorems/5a511e57-6d95-44e4-a6f1-f71cdde53624
-- title:
--   Dedekind Zeta: mixed Embedding norm inv
-- statement:
--   **Inversion sends `|N(x)| ↦ |N(x)|⁻¹`** (the standard treatment: the kernel of the Mellin
--   principle). The absolute norm `N : K_ℝ → ℝ` of the standard treatment inverts under the
--   componentwise inversion `x ↦ x⁻¹` of `K_ℝ^*`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L637-L640
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L637-L640

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

theorem DedekindZeta.mixedEmbedding_norm_inv (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ := by sorry
