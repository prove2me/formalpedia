-- Prove2me | Theorems.Thm_DedekindZeta_GammaIntegral_integrable_gaussian_mellin
-- name    : DedekindZeta.GammaIntegral.integrable_gaussian_mellin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:16.046705+00:00
-- url     : https://prove2.me/theorems/3e3c2478-421c-4159-80e0-8fecc51a11a5
-- title:
--   Gamma Integral: integrable gaussian mellin
-- statement:
--   **Convergence** (the standard treatment): for `0 < s.re` the Gaussian Mellin integrand
--   is integrable for the multiplicative Haar measure on `K_ℝ^*`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L309-L321
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/GammaIntegral.lean#L309-L321

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

theorem DedekindZeta.GammaIntegral.integrable_gaussian_mellin {s : ℂ} (hs : 0 < s.re) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K => gaussian K x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mulHaar K) := by sorry
