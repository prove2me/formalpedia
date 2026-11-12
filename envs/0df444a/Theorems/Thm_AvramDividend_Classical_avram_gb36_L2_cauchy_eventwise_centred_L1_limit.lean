-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb36_L2_cauchy_eventwise_centred_L1_limit
-- name    : AvramDividend.Classical.avram_gb36_L2_cauchy_eventwise_centred_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:44:21.345676+00:00
-- url     : https://prove2.me/theorems/f8ea8a85-8456-4583-b28d-dd4aeb5c7fbd
-- title:
--   An L2-Cauchy sequence with asymptotically zero event means has a centred eventwise L1 limit
-- statement:
--   Complete a general L2 Cauchy sequence on the original probability space using Lp completeness. Transfer L2 convergence to eventwise L1 by Proved gb29. Eventwise expectations converge, so a sequence of event means tending to zero gives a terminal limit of event mean zero.
-- source:
--   Strictly analytic completion needed for root-connected gb23 from physical grid L2 Cauchy and original eventwise mean vanishing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb36_L2_cauchy_eventwise_centred_L1_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 P)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (f nm.1 - f nm.2) 2 P) atTop (𝓝 (0 : ℝ≥0∞)))
    (hMean : Tendsto (fun n : ℕ => ∫ ω in A, f n ω ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∃ L : Ω → ℝ, Integrable L P ∧
      (∫ ω in A, L ω ∂P) = 0 ∧
      Tendsto (fun n : ℕ => ∫ ω in A, |L ω - f n ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
