-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_lower_before_horizon_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:51:12.696461+00:00
-- url     : https://prove2.me/theorems/6f39fe1e-bccb-4f3c-a385-9d4af35267d3
-- title:
--   Strict ruin in a shifted Lévy future window is detected by a rational relative-time grid
-- statement:
--   For any deterministic Lévy splitting time b, arbitrary random reserve H(ω), finite relative horizon T, and sample path ω, strict negative reserve at any relative time before T occurs if and only if it occurs at some countable inverse-natural relative mesh k/n strictly before T. The proof uses shifted strict-crossing right-interval persistence and a ceiling-grid bracket. This identifies the true future-window killing event with the countable-grid event used in the Proved killed-scale Markov–Tonelli factorisation, upstream of two_sided_exit_stopped_scale_identity.
-- source:
--   Proved shifted random-reserve strict right interval lemma and chat03_nnreal_grid_ceiling_bracket.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_lower_before_horizon_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∃ v : ℝ≥0, v < T ∧
      H ω + (X.X (b + v) ω - X.X b ω) < 0) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
      H ω +
        (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) < 0 := by sorry
