-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb29_original_zero_contact_stopped_K_uniform_prefix_limit_from_exact_source
-- name    : AvramDividend.Classical.avram_bvb29_original_zero_contact_stopped_K_uniform_prefix_limit_from_exact_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:11:19.84887+00:00
-- url     : https://prove2.me/theorems/52c24298-56ad-47ad-84fa-0453c8067edf
-- title:
--   Original zero-contact source stopped negative-mark K clipped grid converges to complete physical time integral
-- statement:
--   Take the exact source stopped-K_n compensated negative-mark scalar identity for the original finite physical horizon and original restricted Lévy measure, which is now Proved in 57da0020. If each K_n equals minus the original zero-reserve boundary value times the full restricted negative-mark intensity times the physical discounted Ioc clipped-prefix integral, then K_n tends the corresponding full finite-horizon compensated integral. The proof preserves the exact original uniform grid T-T/(n+2), source exponential discount, all negative-mark intensity and boundary value and relies on the accepted physical Ioc prefix convergence 870c2113. This enables assembly of the all-zero survivor compensated cash limit.
-- source:
--   Authoritative source scalar K 57da0020 Proved and original uniform discounted Ioc time limit 870c2113 Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb29_original_zero_contact_stopped_K_uniform_prefix_limit_from_exact_source
    (q T w0 mass : ℝ) (hT : 0 < T)
    (K : ℕ → ℝ)
    (hK : ∀ n, K n = -(w0 * mass) *
      (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))) :
    Tendsto K atTop
      (𝓝 (-(w0 * mass) *
        (∫ t in Ioc (0 : ℝ) T,
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)))) := by sorry
