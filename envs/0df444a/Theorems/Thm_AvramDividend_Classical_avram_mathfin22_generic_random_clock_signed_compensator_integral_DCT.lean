-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
-- name    : AvramDividend.Classical.avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:25:17.479112+00:00
-- url     : https://prove2.me/theorems/0aab7fb2-d858-4a1f-b40e-49d0c9269db5
-- title:
--   Dominated L1 convergence for true stopped physical signed marks with bounded random Lévy compensator clocks
-- statement:
--   Generic real Bochner integral dominated convergence for approximations to original physical stopped marked-jump integrals with a random bounded clock. The raw approximating pathwise integrals F_k converge to J, uniformly bounded by a common integrable nonnegative jump-count envelope N. The deterministic Lévy intensity compensators c_k converge to r and their absolute values are bounded by M; a measurable random clock ρ stays between zero and T. The signed compensated processes F_k - ρ c_k have one common L1 dominating envelope N+T M, hence their expected values converge exactly to that of the limiting physical signed compensated integral J-ρ r. The proof uses pinned Mathlib dominated Bochner integral convergence, with no stochastic independence, finite total jump intensity, or synthetic Poisson point process assumptions. It provides a reusable bridge from accepted stopped finite-simple mark mean zero to original stopped true z-weighted martingale reward centring.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
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
    (hcConv : Tendsto c atTop (𝓝 r)) :
    Tendsto (fun k => ∫ ω, F k ω - ρ ω * c k ∂P)
      atTop (𝓝 (∫ ω, J ω - ρ ω * r ∂P)) := by sorry
