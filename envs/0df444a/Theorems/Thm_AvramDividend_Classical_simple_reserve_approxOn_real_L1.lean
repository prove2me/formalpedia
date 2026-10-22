-- Prove2me | Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_real_L1
-- name    : AvramDividend.Classical.simple_reserve_approxOn_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:06:20.008413+00:00
-- url     : https://prove2.me/theorems/581ebb8d-397f-4033-a648-e30738a53c27
-- title:
--   Finite-valued measurable real-reserve approximations converge in ordinary L1
-- statement:
--   For any measurable integrable real-valued random reserve Z, construct its canonical Mathlib SimpleFunc.approxOn sequence on the measurable finite-valued range approximation of Z (with zero as a basepoint). Prove that the ordinary expected absolute approximation error tends to zero. Use the exact pinned SimpleFunc.tendsto_approxOn_range_L1_enorm and SimpleFunc.integrable_approxOn_range theorems and the Chat 08 real_L1_integral_tendsto_zero_of_enorm bridge, once remotely Proved. This construction supplies finite-valued measurable approximants needed to pass the previously Proved finite-valued conditional Lévy Markov identity to general integrable reserves; applying it in the past filtration requires trimming the probability measure. The result concerns the canonical simple-function approximation, not stochastic stopping or HJB verification.
-- source:
--   Pinned Mathlib SimpleFunc.integrable_approxOn_range and tendsto_approxOn_range_L1_enorm; dependency-gated real_L1_integral_tendsto_zero_of_enorm at target 28554286-6939-4ef6-b9ae-24f347b84302.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_real_L1_integral_tendsto_zero_of_enorm

open Filter MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.simple_reserve_approxOn_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hI : Integrable Z P) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, |(SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0
          (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by sorry
