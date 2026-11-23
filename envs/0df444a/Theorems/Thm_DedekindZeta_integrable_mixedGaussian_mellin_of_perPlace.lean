-- Prove2me | Theorems.Thm_DedekindZeta_integrable_mixedGaussian_mellin_of_perPlace
-- name    : DedekindZeta.integrable_mixedGaussian_mellin_of_perPlace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:19.9151+00:00
-- url     : https://prove2.me/theorems/44d933e0-730a-4773-9d53-c61a94b47180
-- title:
--   Dedekind Zeta: integrable mixed Gaussian mellin of per Place
-- statement:
--   **`withDensity` + product-measure reduction for the Gaussian Mellin integrand**
--   (the standard treatment). Reduces whole-space integrability of `g(x)·N(x)^s` against
--   `mixedMulHaar K` to the per-place 1D integrabilities `hr`, `hc` (with `σ := s.re`).
--   Established at the `Statements` layer (rather than cited from `GammaIntegral`,
--   which imports this file). Route: `mixedMulHaar = volume.withDensity (...)`, reduce
--   via `integrable_withDensity_iff_integrable_smul'`, dominate the integrand by the
--   place-wise product `(2/π)^{r₂}·∏ f_ℝ·∏ f_ℂ` (equal off the null locus `N(x)=0`),
--   which is `volume`-integrable by `Integrable.fintype_prod`/`Integrable.mul_prod`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1716-L1826
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1716-L1826

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
set_option maxHeartbeats 1600000

theorem DedekindZeta.integrable_mixedGaussian_mellin_of_perPlace {s : ℂ} (hs : 0 < s.re)
    (hr : MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (s.re - 1)) volume)
    (hc : MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (s.re - 1)))
        volume) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by sorry
