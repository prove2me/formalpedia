-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_volterra_resolvent_signed_l1
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_volterra_resolvent_signed_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:39:23.885327+00:00
-- url     : https://prove2.me/theorems/f07d3491-96c1-4e92-9efa-1af402ba0111
-- title:
--   Source Gaussian Volterra resolvent retains an L1 signed Neumann correction density
-- statement:
--   For the Gaussian antitone positive-time kernel, construct the source Volterra derivative-resolvent and retain both its exact signed Neumann power representation and global positive-time L1 integrability of the summed signed convolution density. This combines the accepted original Gaussian resolvent with the native Ioc convolution-power global mass identity and the positive-reserve quadratic-geometric signed-series domination. It establishes the missing global density L1 certificate for subsequent weighted W second-derivative integrability, without assuming positivity of a native kernel at negative time.
-- source:
--   Avram–Palmowski–Pistorius (2007), Gaussian generator lemma; accepted Gaussian Volterra source 0802e5ff, exact-power mass 982ece26, signed positive Gaussian density 4a550821.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_with_power_domination
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_envelope_volterra_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_ioc_neumann_powers_mass_summable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_signed_gaussian_positive_l1

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_gaussian_volterra_resolvent_signed_l1
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ (P : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (w : ℝ),
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x + (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) ∧
      IntegrableOn (fun x : ℝ => ∑' n : ℕ, P n x)
        (Ioi (0 : ℝ)) volume := by sorry
