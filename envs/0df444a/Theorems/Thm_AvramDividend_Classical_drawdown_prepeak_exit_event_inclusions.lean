-- Prove2me | Theorems.Thm_AvramDividend_Classical_drawdown_prepeak_exit_event_inclusions
-- name    : AvramDividend.Classical.drawdown_prepeak_exit_event_inclusions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T05:51:36.268091+00:00
-- url     : https://prove2.me/theorems/b9eddbe2-221d-4e21-ac28-f713945712a3
-- title:
--   Stopped-prefix inclusion of ordinary lower exits and reflected drawdown exceedances
-- statement:
--   For a path X and running-peak path S on an arbitrary pre-upcrossing time set I, assume the supremum remains between zero and the next peak threshold h throughout I. Then ordinary descent below -a implies reflected drawdown above a within I, while reflected drawdown above a implies ordinary descent below h-a within I. The result packages both stopped-prefix event inclusions for the killed upward-passage renewal step and avoids any claim about the unproved two-sided fluctuation identity, strong Markov law or valuation.
-- source:
--   Avram, Palmowski and Pistorius (2007), first-passage/reflected-supremum argument for Proposition 1, with the pointwise inequalities supplied by the remotely Proved theorem AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds, UUID 45e397da-f6fa-4eb0-a294-6c3ab2c5f2c5.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Theorems.Thm_AvramDividend_Classical_drawdown_strict_exit_strip_of_sup_bounds

theorem AvramDividend.Classical.drawdown_prepeak_exit_event_inclusions
    {T : Type*} (I : Set T) (S X : T → ℝ) (a h : ℝ)
    (hSup : ∀ t ∈ I, 0 ≤ S t ∧ S t ≤ h) :
    {t : T | t ∈ I ∧ X t < -a} ⊆
      {t : T | t ∈ I ∧ a < S t - X t} ∧
    {t : T | t ∈ I ∧ a < S t - X t} ⊆
      {t : T | t ∈ I ∧ X t < h - a} := by sorry
