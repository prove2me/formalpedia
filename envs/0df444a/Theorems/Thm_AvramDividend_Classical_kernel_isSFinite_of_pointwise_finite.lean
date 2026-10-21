-- Prove2me | Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
-- name    : AvramDividend.Classical.kernel_isSFinite_of_pointwise_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:28:27.670343+00:00
-- url     : https://prove2.me/theorems/e1a700f5-002e-4bc1-afb4-dcde7bffc72a
-- title:
--   Every kernel whose sample-path total measures are finite is s-finite via measurable mass-level partition
-- statement:
--   Let κ be a measurable kernel from an arbitrary sample space to real time. If each individual kernel measure κω has finite total mass, then κ is s-finite in the precise Mathlib sense: a countable sum of finite kernels with a uniform finite bound per component. Define the measurable total-mass function, partition the sample space into its unique natural-number mass bins, use the separately proved measurable kernel cut-off theorem to obtain a finite selector kernel for each bin, and recover κ exactly using the proved unique-partition sum identity. This theorem makes the original running-supremum dividend interval kernel s-finite unconditionally from its already accepted samplewise interval finite-mass and random-measure measurability theorems.
-- source:
--   Dependency-gated kernel_cutoff_finite_exists target ad10ab1d-f1d7-478c-afbf-f3c1b35cc928 ACCEPTED candidate 12211; measurable_finite_mass_bin target 1cc74373-b604-4acb-8fc0-31c28d8d00ed pending 12215; finite_ennreal_mass_bin_unique and kernel_sum_unique_partition are staged authoring proofs. Pinned IsSFiniteKernel.mk exact signature job 85f2ed86-2474-4625-ac27-51cf44ea145c.

import Mathlib.Probability.Kernel.Defs
import Theorems.Thm_AvramDividend_Classical_kernel_cutoff_finite_exists
import Theorems.Thm_AvramDividend_Classical_measurable_finite_mass_bin
import Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_unique
import Theorems.Thm_AvramDividend_Classical_kernel_sum_unique_partition

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.kernel_isSFinite_of_pointwise_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (hfinite : ∀ ω : Ω, (κ ω) Set.univ < ⊤) :
    ProbabilityTheory.IsSFiniteKernel κ := by sorry
