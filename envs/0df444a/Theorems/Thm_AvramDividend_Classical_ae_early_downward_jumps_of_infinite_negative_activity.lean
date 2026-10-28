-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_infinite_negative_activity
-- name    : AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T23:08:00.656215+00:00
-- url     : https://prove2.me/theorems/ff758fb4-87e5-4eec-b153-b6135498ca04
-- title:
--   Infinite negative jump activity gives a.s. arbitrarily early downward jumps
-- statement:
--   Infinite intensity of negative Lévy jumps implies infinitely many genuine downward sample-path jumps on every positive interval. Use finite annular jump bands and their compound-Poisson count laws, then a null no-jump estimate and a countable shrinking-horizon argument. Applies irrespective of bounded variation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3 and zero-barrier discussion, https://arxiv.org/pdf/math/0702893. Proved conditional lemmas zero_probability_of_poisson_count_no_jump_event and ae_early_downward_jumps_of_null_no_jump_grid. The Poisson-band count law requires an independent construction from the exact SpectrallyNegativeLevy axioms.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.Instances.ENNReal.Lemmas
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_early_downward_jumps_of_infinite_negative_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l := by sorry
