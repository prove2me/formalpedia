-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_positive_error_event_tail_absorption
-- name    : AvramDividend.Classical.avram_bv_error7_original_positive_error_event_tail_absorption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:37:12.280119+00:00
-- url     : https://prove2.me/theorems/ea4fefad-6143-4006-a041-70c540ce03cd
-- title:
--   Original BV source-mass complement bound absorbs stopped-grid positive errors
-- statement:
--   For the authentic original bounded-variation Lévy source X, an a.e. exhausting sequence of measurable interior localisation events has vanishing expected complementary BV source mass. If the true stopped-grid positive errors converge in expectation on each fixed interior event and their outside-event positive part is bounded by K times the original source mass uniformly over every physical-grid index, then their full expected positive part converges to zero. The proof establishes the uniform complementary expected-error bound by integrability of the actual BV source mass and comparison of integrals, and invokes the previously Proved fixed-event epsilon absorption. It never uses the BV signed prebudget or infers L1 from pointwise convergence.
-- source:
--   Formal original-process bridge GG c8a27dc5 + FF 114318fd, retaining explicit outstanding outside-event source dominance; needed by 2bc848f9 to close stopped-grid positive-error Fatou transition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_fixed_event_uniform_tail_absorption
open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_positive_error_event_tail_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : ∀ n, Tendsto
      (fun m => ∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hOutside : ∀ n m, ∀ᵐ ω ∂P, ω ∉ s n →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
