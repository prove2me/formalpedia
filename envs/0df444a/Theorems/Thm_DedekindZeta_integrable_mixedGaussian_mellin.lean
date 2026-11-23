-- Prove2me | Theorems.Thm_DedekindZeta_integrable_mixedGaussian_mellin
-- name    : DedekindZeta.integrable_mixedGaussian_mellin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:24:08.554804+00:00
-- url     : https://prove2.me/theorems/254b8cda-19be-437c-b815-b852a431ca53
-- title:
--   Dedekind Zeta: integrable mixed Gaussian mellin
-- statement:
--   **Whole-space Gaussian Mellin convergence** (the standard treatment). For `0 < s.re` the
--   base Minkowski Gaussian Mellin integrand `g(x)·N(x)^s` is `mixedMulHaar`-integrable
--   on `K_ℝ^*`. Established at the `Statements` layer (mirror of
--   `GammaIntegral.integrable_gaussian_mellin`, which lives downstream and so cannot
--   be cited here) by feeding the per-place 1D helpers into the product-measure
--   reduction. NB: this is against the canonical upstream `mixedGaussian`/`mixedMulHaar`
--   objects, whereas `GammaIntegral.integrable_gaussian_mellin` is the legacy
--   `gaussian`/`mulHaar` form; both reuse the single-home generic 1D helpers
--   (`integrable_real_gaussian_mul_abs_rpow`, `integrable_complexPlace_gaussian_rpow`)
--   defined here, so no generic analysis lemma is duplicated.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1838-L1845
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1838-L1845

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding

theorem DedekindZeta.integrable_mixedGaussian_mellin {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by sorry
