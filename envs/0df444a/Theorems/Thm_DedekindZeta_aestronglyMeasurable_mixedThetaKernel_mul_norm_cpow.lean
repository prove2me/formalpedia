-- Prove2me | Theorems.Thm_DedekindZeta_aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
-- name    : DedekindZeta.aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:43:26.318696+00:00
-- url     : https://prove2.me/theorems/9c049d9d-dd83-46db-90cf-b642ec0e31f0
-- title:
--   Dedekind Zeta: aestrongly Measurable mixed Theta Kernel mul norm cpow
-- statement:
--   **Measurability of the fractional theta integrand.**
--   For any fractional ideal `I` and any `t : ℂ`, the integrand
--   `y ↦ Θ(I, y)·N(y)^t` is `AEStronglyMeasurable` against `mixedMulHaar K`.
--
--   `Theta.mixedThetaKernel K I` is the `∑'` over the countable index
--   `{a : K // a ∈ I ∧ a ≠ 0}` of the summands `y ↦ (mixedGaussian K (y·σa) : ℂ)`,
--   each (strongly) measurable (mirroring
--   `GammaIntegral.aestronglyMeasurable_mixedGaussian_mul_norm_cpow`); the `∑'` of
--   (AE)strongly-measurable functions over a countable index is (AE)strongly
--   measurable (`AEStronglyMeasurable.tsum`). Multiplying by the measurable norm power
--   `N(y)^t` keeps it measurable. This part does **not** use `1 < t.re`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1483-L1506
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L1483-L1506

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

theorem DedekindZeta.aestronglyMeasurable_mixedThetaKernel_mul_norm_cpow
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y => Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ t)
      (mixedMulHaar K) := by sorry
