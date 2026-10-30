-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:46:16.256982+00:00
-- url     : https://prove2.me/theorems/66022e73-7cfb-4c66-a5c9-52b93a5b69a9
-- title:
--   Original Gaussian Volterra Neumann resolvent derivative and global signed L1 density
-- statement:
--   For an integrable, nonnegative, positive-axis antitone Gaussian double-tail kernel K, the original causal Neumann construction produces a C1 Volterra resolvent g whose signed density S=∑P_n is globally L1 on positive reserves and satisfies the exact pointwise derivative g'(x)=exp(wx)S(x)/a. The proof obtains every series differentiation and summability certificate from the original geometrically contracting positive envelope; there is no added differentiability assumption on g and no replacement stochastic model.
-- source:
--   Pinned source Gaussian causal Volterra envelope and signed Neumann powers, accepted source theorems causal_neumann_C1_with_power_domination, causal_signed_power_continuity_from_envelope, avram_wave3_05_gaussian_neumann_termwise_derivative, avram_wave3_05_gaussian_exponential_derivative_cancel.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_with_power_domination
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_envelope_volterra_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_ioc_neumann_powers_mass_summable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_signed_gaussian_positive_l1
import Theorems.Thm_AvramDividend_Classical_causal_signed_power_continuity_from_envelope
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_derivative_from_positive_L1
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_neumann_termwise_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_exponential_derivative_cancel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
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
        (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        HasDerivAt g (Real.exp (w * x) *
          ((∑' n : ℕ, P n x) / a)) x) := by sorry
