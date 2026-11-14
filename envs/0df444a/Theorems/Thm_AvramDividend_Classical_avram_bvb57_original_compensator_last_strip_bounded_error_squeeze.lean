-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb57_original_compensator_last_strip_bounded_error_squeeze
-- name    : AvramDividend.Classical.avram_bvb57_original_compensator_last_strip_bounded_error_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:34:00.841202+00:00
-- url     : https://prove2.me/theorems/5e1c647f-f941-43b8-982a-7bdf0d562919
-- title:
--   Any original physical last-strip compensated error uniformly squeezed by a constant times finite Levy intensity and mesh width vanishes
-- statement:
--   For the actual source finite negative Levy intensity and its exact final uniform physical time strip, any signed compensated terminal error admitting the explicit two-sided deterministic bound ±K times intensity multiplied by T/(n+2) converges to zero. This bounded-error transfer lemma allows a genuinely source-preserving original BV BVB49/BVB55 proof to eliminate a final-strip predictable compensator term once the integrand is bounded; unlike omitting that compensator it accounts for it quantitatively.
-- source:
--   Previously Proved original BVB52 final strip intensity times width limit and order-topology squeeze theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb57_original_compensator_last_strip_bounded_error_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (K : ℝ) (e : ℕ → ℝ)
    (hE : ∀ n : ℕ,
       -(K * ((X.ν (Iio (0 : ℝ))).toReal *
         (T / ((n : ℝ) + 2)))) ≤ e n ∧
       e n ≤ K * ((X.ν (Iio (0 : ℝ))).toReal *
         (T / ((n : ℝ) + 2)))) :
    Tendsto e atTop (𝓝 (0 : ℝ)) := by sorry
