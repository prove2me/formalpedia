-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a332_eventual_ae_small_modulus_uniform_expected_energy_budget
-- name    : AvramDividend.Classical.avram_ga_a332_eventual_ae_small_modulus_uniform_expected_energy_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:25:38.945199+00:00
-- url     : https://prove2.me/theorems/b76b8c96-a6d8-45aa-8389-d538b5e465b4
-- title:
--   Eventual almost-sure small Gaussian modulus bound plus uniformly integrable raw energy gives arbitrarily small expected positive source
-- statement:
--   For a finite-cell Gaussian source with integrable positive part, if the raw quadratic energy has a uniform expected bound and the other integrable source corrections vanish in expected L1, then an eventual almost-sure small-raw-increment positive bound by epsilon times energy plus those corrections implies arbitrarily small expected positive source for an appropriate threshold delta. Both the mask inequality and the mesh drift restriction may hold only for sufficiently refined levels, and the Taylor hypothesis may hold only almost surely. This closes the gap between source-specific a194/a236/a244 and the required a264 small-cell expected bound.
-- source:
--   Original zerojump Gaussian stopped physical a264; refinement of a279 to eventually a.e. source inequalities

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a332_eventual_ae_small_modulus_uniform_expected_energy_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Small : ℝ → ℕ → Ω → ℝ)
    (E A B : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hSI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (Small δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ m, Integrable (B m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hAL : Tendsto (fun m => ∫ ω, A m ω ∂P)
      atTop (𝓝 (0:ℝ)))
    (hBL : Tendsto (fun m => ∫ ω, B m ω ∂P)
      atTop (𝓝 (0:ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
        ∀ᵐ ω ∂P,
          max (Small δ m ω) 0 ≤
            ε*E m ω+A m ω+B m ω) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧ ∃ k : ℕ,
      ∀ m : ℕ, k ≤ m →
        (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by sorry
