-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock
-- name    : AvramDividend.Classical.avram_p3_comp8_original_BV_source_tail_L1_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:17:23.125202+00:00
-- url     : https://prove2.me/theorems/99493040-c824-4628-8b19-13b26a4ef0ca
-- title:
--   Original bounded-variation Lévy source mass on shrinking localisation complements converges in L1 at arbitrary horizon
-- statement:
--   For the original BV Lévy process and any finite horizon T, a.e. eventual exhaustion by measurable localisation events forces the expected original source-mass envelope on the complement to vanish. This is the source-exact arbitrary-T extension of Proved BV-ERROR7 tail exhaustion, using dominated convergence and all-horizon mass integrability.
-- source:
--   Source-faithful adaptation of Proved c8a27dc5; deletes the T≤1 assumption and substitutes the independently derived all-T L1 BV source mass.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The authentic BV source-mass first moment on shrinking complements of
an a.e. exhausting measurable localisation tends to zero. -/

theorem AvramDividend.Classical.avram_p3_comp8_original_BV_source_tail_L1_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) :
    (∀ n, Integrable
      (fun ω => if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
    Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
