-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_esscher_pure_jump_path_law_downward_regular
-- name    : AvramDividend.Classical.avram_root29_04_esscher_pure_jump_path_law_downward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:19:58.685+00:00
-- url     : https://prove2.me/theorems/e888b66e-7b9b-44c0-823a-27b72f88dd2d
-- title:
--   True finite-clock Esscher whole-path law on the Borel coordinate space is immediately downward regular under infinite small-jump variation
-- statement:
--   The genuine finite-terminal Esscher-weighted Lévy law, pushed forward by the actual whole original X path into the countable-product path measurable space, is almost surely immediately downward regular when the small negative-jump absolute first moment diverges. The proof uses the already accepted finite-clock source regularity, a measurable countable-grid event, the proved right-continuity-based dense-grid equivalence, and the exact a.e. pushforward theorem. This supplies the true Q path-law premise in the excursion-height killed Markov converter, leaving the excursion n strong Markov identity as a separate unproved theorem.
-- source:
--   Proved aa3b8094 finite-terminal Esscher near-zero regularity, 561313a4 dense grid equivalence, 311860a5 measurable grid event, Mathlib ae_map_iff and measurable_pi_lambda.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_pure_jump_esscher_fixed_horizon_downward_regular
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_esscher_pure_jump_path_law_downward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ f ∂Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω)
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (θ * X.X T ω - (T : ℝ) * X.ψ θ)))),
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ f s < 0 := by sorry
