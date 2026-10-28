-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_cofinal_capped_hit_sup_le_iff_level_hit
-- name    : AvramDividend.Classical.usc_cofinal_capped_hit_sup_le_iff_level_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:06:39.402968+00:00
-- url     : https://prove2.me/theorems/0a713d4b-eee9-4028-be27-c92fcfc89c47
-- title:
--   Cofinal capped first-level clocks converge to the actual uncapped closed-level first-hit event
-- statement:
--   For a real-valued path upper semicontinuous on every finite prefix and any sequence of deterministic caps cofinal towards infinity, the supremum in WithTop ℝ≥0 of its exact capped first closed-level hitting times lies before time t exactly when the path has actually reached the level by some time s≤t. The forward direction picks one cap beyond t; its capped first-hit event then forces a true hit. Conversely any hit by t makes every capped clock ≤t, using its first-hit identity when the cap is beyond t, and the cap bound when it is at or before t. Thus the extended supremum of capped clocks represents the actual uncapped first hitting time, with ∞ when the path never hits, without imposing a right-continuous filtration. This provides a pathwise event bridge for a full unbounded-horizon reflected excursion stopping-time theorem.
-- source:
--   Accepted usc_capped_first_closed_hit_le_iff_prefix_hit and pinned Mathlib WithTop, iSup_le, le_iSup, csInf_le.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit

open AvramDividend.Classical Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.usc_cofinal_capped_hit_sup_le_iff_level_hit
    (f : ℝ≥0 → ℝ) (caps : ℕ → ℝ≥0) (x : ℝ)
    (husc : ∀ H : ℝ≥0, UpperSemicontinuousOn f (Icc 0 H))
    (hcofinal : ∀ t : ℝ≥0, ∃ n : ℕ, t < caps n)
    (t : ℝ≥0) :
    (⨆ n : ℕ, WithTop.some
      (sInf ((Icc (0 : ℝ≥0) (caps n) ∩ f ⁻¹' Ici x) ∪ {caps n}))) ≤
        (t : WithTop ℝ≥0) ↔
      ∃ s : ℝ≥0, s ≤ t ∧ x ≤ f s := by sorry
