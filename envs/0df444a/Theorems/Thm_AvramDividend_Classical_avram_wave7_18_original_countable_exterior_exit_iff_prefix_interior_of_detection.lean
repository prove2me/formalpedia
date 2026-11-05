-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
-- name    : AvramDividend.Classical.avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:55:59.718124+00:00
-- url     : https://prove2.me/theorems/4a4b57ad-a49a-40f2-aaa6-1be2683fac2e
-- title:
--   Original reserve continuous-prefix interior is equivalent to countable observed exit clock lower bound under detection
-- statement:
--   Take the genuine controlled Lévy reserve Z_t=x+X.X t-rightLimit D t and the infimum σ of deterministic sample times r_k at which Z leaves the closed band [lower,upper] strictly; if no sample exits, the corresponding clock is ⊤. Assume the explicit detection property: whenever Z_s strictly exits at some s<t, some sample r_k<t also strictly exits. Then for any sample path and deterministic time T, all reserve values Z_t for t<T lie in [lower,upper] if and only if T≤σ. The forward implication follows from each gated sample clock; the reverse uses detection and iInf_le to contradict a detected exit before T. This is a conditional, source-specific bridge from countable observation stopping times to a true continuous-time path prefix. The detection condition must later be discharged using the Proved right-continuous reserve and a dense time family; no unrelated probability space or assumptions about Itô compensation are introduced.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hdetect : ∀ ω (s t : ℝ≥0), s < t →
      (x + X.X s ω - rightLimit D s ω < lower ∨
        upper < x + X.X s ω - rightLimit D s ω) →
      ∃ k, r k < t ∧
        (x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω)) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (∀ t : ℝ≥0, t < T →
        lower ≤ x + X.X t ω - rightLimit D t ω ∧ x + X.X t ω - rightLimit D t ω ≤ upper) ↔
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) := by sorry
