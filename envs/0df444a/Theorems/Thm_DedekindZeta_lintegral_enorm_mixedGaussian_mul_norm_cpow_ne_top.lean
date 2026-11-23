-- Prove2me | Theorems.Thm_DedekindZeta_lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
-- name    : DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:24.734456+00:00
-- url     : https://prove2.me/theorems/57e56836-771d-41b2-9068-3f50a9799350
-- title:
--   Dedekind Zeta: lintegral enorm mixed Gaussian mul norm cpow ne top
-- statement:
--   **Whole-space Gaussian Mellin `enorm` finiteness**
--   (helper 2). For `1 < t.re` the whole-space
--   `enorm`-`lintegral` of the base Minkowski Gaussian Mellin integrand
--   `g(x)·N(x)^t` is finite:
--
--       ∫⁻ x, ‖g(x)·N(x)^t‖ₑ d^*x ≠ ∞.
--
--   This is the `M`/`|I(t)|` archimedean Gamma-factor finiteness: Gaussian decay at
--   the large-norm end controls the `N → ∞` tail, and the condition `Re t > 1`
--   governs convergence at the small-norm end. It is the genuine convergence input
--   (the `1 < Re t` threshold) feeding the fractional-ideal assembly.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1860-L1867
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1860-L1867

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

theorem DedekindZeta.lintegral_enorm_mixedGaussian_mul_norm_cpow_ne_top
    {t : ℂ} (ht : 1 < t.re) :
    ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) ≠ ∞ := by sorry
