-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
-- name    : AvramDividend.Classical.avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:20:27.034214+00:00
-- url     : https://prove2.me/theorems/259111d7-391a-4933-9755-f3e94c3bc65d
-- title:
--   Gaussian small-source selected-threshold integrability and arbitrary positive expected budget from a.e. Taylor modulus and two vanishing source errors
-- statement:
--   Given measurable positive small-increment source S, an integrable raw Gaussian energy E with uniform expected upper bound K, an integrable Hessian cross source A whose expectation vanishes, and for each positive ε an integrable discount Young correction source B_ε whose expectation vanishes, suppose the original small Taylor analysis supplies a threshold δ with an almost-everywhere upper bound Sδ ≤ ε E + A + Bε at every physical mesh. Then for each requested error η one can select a δ for which the positive source is integrable at every mesh and has expected value at most η eventually. This is the precise quantitative bridge needed to close the original a361 Gaussian small-full-cell obligation.
-- source:
--   Original a194 Taylor modulus, a290 full masked Young source, a240/a243 raw energy, a214 cross L1, a284 discount width, a342 small source aestrong measurability and a363 source-integrability.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ → ℕ → Ω → ℝ)
    (E A : ℕ → Ω → ℝ) (B : ℝ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hSm : ∀ δ, 0 < δ → ∀ m,
      AEStronglyMeasurable (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ ε, 0 < ε → ∀ m, Integrable (B ε m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hAL : Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hBL : ∀ ε, 0 < ε →
      Tendsto (fun m => ∫ ω, B ε m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ m, ∀ᵐ ω ∂P,
        max (S δ m ω) 0 ≤
          ε * E m ω + A m ω + B ε m ω) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧
      (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
      ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η := by sorry
