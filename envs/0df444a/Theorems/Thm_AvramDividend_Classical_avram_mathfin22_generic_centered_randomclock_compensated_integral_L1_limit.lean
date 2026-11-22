-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
-- name    : AvramDividend.Classical.avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:49:57.656489+00:00
-- url     : https://prove2.me/theorems/8e787299-f9d3-4c85-bbff-fda3ca6ca281
-- title:
--   Dominated countably stopped signed marked-noise mean zero passes to L1 physical mark limit
-- statement:
--   A general measure-theoretic closure theorem required for the original Avram stopped true z-weighted signed jump source. Under a fixed integrable random-clock envelope N and a bounded integrable clock ρ, let the original finite-simple signed mark integrals F_k converge almost everywhere to true marked physical integral J, while finite-simple Lévy compensator intensities c_k converge to r. Assuming every F_k is L1 integrable, finite-simple signed compensated integrals have exactly zero expectation, and both intensity and raw mark amplitudes obey their original common domination, prove J-ρr integrable and its expected signed value zero. L1 integrability of J is deduced from the ae limiting strong measurability and dominated norm bound. Its expected zero then follows by the previously proved random-clock Bochner compensated DCT theorem. This generic lemma has no Poisson-process model, finite activity assumption or synthetic stochastic hypotheses and will simplify the source-specific original negative-band stopped z-weighted proof.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (J N ρ : Ω → ℝ)
    (c : ℕ → ℝ) (r M T : ℝ)
    (hT : 0 ≤ T)
    (hFI : ∀ k, Integrable (F k) P)
    (hNI : Integrable N P) (hρI : Integrable ρ P)
    (hρ : ∀ ω, 0 ≤ ρ ω ∧ ρ ω ≤ T)
    (hFBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ N ω)
    (hcBound : ∀ k, |c k| ≤ M)
    (hFConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (J ω)))
    (hcConv : Tendsto c atTop (𝓝 r))
    (hCentered : ∀ k,
      (∫ ω, F k ω - ρ ω * c k ∂P) = 0) :
    Integrable (fun ω => J ω - ρ ω * r) P ∧
    (∫ ω, J ω - ρ ω * r ∂P) = 0 := by sorry
