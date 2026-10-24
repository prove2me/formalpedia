-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_Ioc_kernel_isFinite_of_uniform_bound
-- name    : AvramDividend.Classical.runningSup_Ioc_kernel_isFinite_of_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:43:04.826911+00:00
-- url     : https://prove2.me/theorems/a0a0b856-226e-4099-82b3-56b062c5a7d6
-- title:
--   Uniformly bounded actual dividend interval mass implies a finite random-measure kernel
-- statement:
--   If the actual running-supremum dividend Stieltjes mass of a fixed interval admits a common finite ENNReal bound across every sample point, the interval-restricted measurable random measure forms a finite kernel. The uniform bound is an explicit hypothesis because samplewise finite Stieltjes mass alone does not imply the Mathlib IsFiniteKernel class. This conditional theorem may be used for uniformly truncated regulators or as one component of a countable s-finite-kernel decomposition.
-- source:
--   Pinned remote compiler signature of ProbabilityTheory.IsFiniteKernel.mk, job 37233ed2-97ca-40a4-92e2-ac8eb183605d, requires ∃ C<⊤, ∀ω, (κ ω) univ ≤ C; proved random-measure measurability target d763694e-e35d-43bf-90d6-3d1a42a067ed.

import Mathlib.Probability.Kernel.Defs
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_Ioc_kernel_isFinite_of_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hBound : ∀ ω : Ω,
       (dividendMeasure (runningSup X) ω) (Set.Ioc s t) ≤ C) :
    ProbabilityTheory.IsFiniteKernel
      (ProbabilityTheory.Kernel.mk
        (fun ω : Ω =>
          (dividendMeasure (runningSup X) ω).restrict (Set.Ioc s t))
        (runningSup_dividendMeasure_restrict_Ioc_measurable X s t)) := by sorry
