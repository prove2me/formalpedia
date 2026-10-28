-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_prefix_path_event_pushforward_transfer
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_prefix_path_event_pushforward_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:08:17.524425+00:00
-- url     : https://prove2.me/theorems/0278f2e6-1001-4a59-b866-87f04e469df3
-- title:
--   Pushforward finite-increment-prefix strict events to sampled path drawdown/infimum events
-- statement:
--   Given a measurable finite-dimensional observation F on a path space, a coordinate extension w with measurable coordinate maps and exact prefix-sum identity relative to sampled path positions Z_k, an equality of strict terminal-minus-prefix and prefix events under the pushed-forward law F_*ν transfers to equality of the corresponding strict path drawdown/infimum event masses under ν. This is a generic measurable pushforward and prefix-telescope identity, independent of Lévy stationarity, Esscher tilting or Wiener–Hopf splitting. It extracts the final measurable-event conversion from the longer Avram 1E-B finite-grid path proof, keeping downstream theorem files short.
-- source:
--   Pinned Mathlib MeasurableSet.iUnion, Finset.measurable_sum and Measure.map_apply, exact prefix sum equalities.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_strict_prefix_path_event_pushforward_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (a : ℝ)
    (F : Ω → (Fin n → ℝ)) (hF : Measurable F)
    (w : (Fin n → ℝ) → ℕ → ℝ)
    (hw : ∀ j : ℕ, Measurable (fun v : Fin n → ℝ => w v j))
    (Z : ℕ → Ω → ℝ)
    (hprefix : ∀ (ω : Ω) (k : ℕ), k ≤ n →
      Finset.sum (Finset.range k) (w (F ω)) =
        Z k ω - Z 0 ω)
    (hLaw :
      (Measure.map F ν)
        {v : Fin n → ℝ | ∃ k : Fin n.succ,
          Finset.sum (Finset.range n) (w v) -
            Finset.sum (Finset.range k.val) (w v) < a} =
      (Measure.map F ν)
        {v : Fin n → ℝ | ∃ k : Fin n.succ,
          Finset.sum (Finset.range k.val) (w v) < a}) :
    ν {ω : Ω | ∃ k : Fin n.succ, Z n ω - Z k.val ω < a} =
    ν {ω : Ω | ∃ k : Fin n.succ, Z k.val ω - Z 0 ω < a} := by sorry
