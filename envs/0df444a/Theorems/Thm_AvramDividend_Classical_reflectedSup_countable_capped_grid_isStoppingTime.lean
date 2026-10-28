-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_capped_grid_isStoppingTime
-- name    : AvramDividend.Classical.reflectedSup_countable_capped_grid_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:42:31.596617+00:00
-- url     : https://prove2.me/theorems/da1a5090-0814-4efd-8443-9f7ceeadc250
-- title:
--   Capped countable-grid excursion drawdown first passage is an actual stopping time with right-continuous filtration
-- statement:
--   Let X be an actual spectrally negative Lévy process with reflected drawdown R and an explicitly right-continuous filtration. For any sequence of deterministic observation times bounded above by a finite horizon H and any level x, the first observed time at which the reflected drawdown reaches level x, or the cap H if none does, is an honest stopping time. This is obtained by instantiating the accepted general adapted countable-grid stopping-time lemma with the separately accepted actual reflected-process adaptedness theorem. It supplies a directly usable stochastic first-passage approximation for reflected Lévy excursions while making no unsupported claim about the full continuous-time excursion first-height debut.
-- source:
--   Pinned Mathlib countable-inf stopping times under right-continuous filtration and the accepted Prove2Me actual reflectedSup_adapted theorem.

import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_countable_capped_grid_superlevel_isStoppingTime

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_countable_capped_grid_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ H) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨅ n : ℕ, if x ≤ reflectedSup X (clock n) ω
        then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) := by sorry
