-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_surface_majorant
-- name    : DedekindZeta.ConeRadialReduction.mixedGaussian_surface_majorant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:39:13.969802+00:00
-- url     : https://prove2.me/theorems/d462fa50-2139-4552-b66f-a8176c5ff8a4
-- title:
--   Cone Radial Reduction: mixed Gaussian surface majorant
-- statement:
--   **Uniform summable Gaussian majorant over the norm-1 surface.** For a nonzero
--   fractional ideal `I` there is a single `S ≥ 0` so that for *every* point `σ` of
--   the norm-1 surface fundamental domain `normEqOneSurface K`, the fixed-`σ`
--   fractional Gaussian lattice sum over the nonzero elements of `I` is summable and
--   bounded by `S`. Mechanism (the standard treatment): on the surface every place-norm
--   `normAtPlace w σ` is bounded above by a uniform `M ≥ 1` (the surface is
--   relatively compact, `isCompact_closure_normEqOneSurface`); since
--   `∏_w normAtPlace w σ ^ mult w = N σ = 1`, each `normAtPlace w σ` is then bounded
--   *below* by `κ = (M^d)⁻¹ > 0` (`d = [K:ℚ]`), uniformly in `σ`. Hence the
--   quadratic exponent obeys `Q_σ(a) ≥ κ² · Q₁(a)`, so every summand is dominated by
--   the single `σ`-independent Gaussian `mixedGaussian K (κ • mixedEmbedding K a)`,
--   whose lattice sum (`summable_mixedGaussian_submodule`) is the uniform `S`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1091-L1228
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L1091-L1228

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

theorem DedekindZeta.ConeRadialReduction.mixedGaussian_surface_majorant (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ σ ∈ normEqOneSurface K,
        Summable (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
            Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ∧
          (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ≤ S := by sorry
