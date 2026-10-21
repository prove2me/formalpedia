-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_pathwise_markov_split
-- name    : AvramDividend.Classical.chat04_closed_horizon_survival_pathwise_markov_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:18:03.418593+00:00
-- url     : https://prove2.me/theorems/75c76580-1762-4af5-8a87-86ebd97db60a
-- title:
--   Split closed-horizon strict survival into historical survival and future-increment-path survival
-- statement:
--   For a spectrally negative Lévy reserve process, real starting reserve x and strict lower/upper barriers, and deterministic times s≤u, exact survival at all continuous times v≤u equals the intersection of survival up to time s and survival over s≤v≤u expressed solely through the post-s reserve x+X_s and the future path increments X_v−X_s. The statement is pathwise and requires no first-passage null events, no diffusion/no-creeping assumptions or expectation bounds. It is the core event splitting needed to apply a killed Markov transition law to the survival indicator. Unlike the previously proved grid density lemmas it connects the past and future killed events across an arbitrary intermediate time, with closed endpoints handled exactly.
-- source:
--   Original canonical SpectrallyNegativeLevy process paths. Pointwise additive reserve identity and totality of ordered times; original Avram two-sided killed Markov verification programme.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_survival_pathwise_markov_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u : ℝ≥0) (hsu : s ≤ u)
    (x lower upper : ℝ) :
    {ω | ∀ v : ℝ≥0, v ≤ u →
      ¬ (x + X.X v ω < lower ∨ upper < x + X.X v ω)} =
      {ω | ∀ v : ℝ≥0, v ≤ s →
        ¬ (x + X.X v ω < lower ∨ upper < x + X.X v ω)} ∩
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ ((x + X.X s ω) + (X.X v ω - X.X s ω) < lower ∨
          upper < (x + X.X s ω) + (X.X v ω - X.X s ω))} := by sorry
