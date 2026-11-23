-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_summable_mixedGaussian_idealKernel
-- name    : DedekindZeta.ConeRadialReduction.summable_mixedGaussian_idealKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:39:36.00232+00:00
-- url     : https://prove2.me/theorems/10a7faaa-c556-4914-b16c-281b04be9fe1
-- title:
--   Cone Radial Reduction: summable mixed Gaussian ideal Kernel
-- statement:
--   **Summability of the integral-kernel Gaussian family** over the nonzero
--   elements of `𝔞` (for any unit point `x`, `N x ≠ 0`): a subfamily of the
--   whole-lattice Gaussian sum `summable_mixedGaussian_submodule`, reindexed through
--   the injection `𝓞 K ↪ K` and brought back to `ℝ` via `Complex.summable_ofReal`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1274-L1294
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1274-L1294

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

theorem DedekindZeta.ConeRadialReduction.summable_mixedGaussian_idealKernel (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    Summable (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
      Theta.mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K))) := by sorry
