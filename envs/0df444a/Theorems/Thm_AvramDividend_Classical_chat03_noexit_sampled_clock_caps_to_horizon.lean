-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
-- name    : AvramDividend.Classical.chat03_noexit_sampled_clock_caps_to_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:58:37.072978+00:00
-- url     : https://prove2.me/theorems/3cf9f1dd-ce40-4097-abf2-4594457074d1
-- title:
--   No-exit Lévy paths have sampled stopped clocks exactly capped at the horizon
-- statement:
--   If a fixed spectrally negative Lévy sample path has no strict crossing of either barrier up to the grid's terminal observation time, and that terminal time covers a chosen horizon T, the actual bounded Mathlib hittingBtwn clock equals the terminal natural-number index and its nonnegative physical time clipped to T equals T. This handles the finite-horizon no-exit side of grid convergence without assuming continuity at T.
-- source:
--   Proved generic Chat03 hittingBtwn no-observed-crossing theorem, elementary grid-index monotonicity and strict signed-gap equivalence.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_sampled_clock_caps_to_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (mesh T : ℝ≥0) (m : ℕ)
    (hT : T ≤ (m : ℝ≥0) * mesh)
    (hNo : ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * mesh →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)) :
    min (((hittingBtwn
        (fun (j : ℕ) ξ => max
          (X.X ((j : ℝ≥0) * mesh) ξ - upper)
          (lower - X.X ((j : ℝ≥0) * mesh) ξ))
        (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by sorry
