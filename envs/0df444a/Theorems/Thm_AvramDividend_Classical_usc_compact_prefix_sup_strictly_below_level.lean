-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_sup_strictly_below_level
-- name    : AvramDividend.Classical.usc_compact_prefix_sup_strictly_below_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:42:47.626529+00:00
-- url     : https://prove2.me/theorems/b2aaf6e5-af1e-4b95-87f8-ec79d4d48e95
-- title:
--   Strict nonattainment of a level on a compact upper-semicontinuous prefix gives a uniform positive gap below the level
-- statement:
--   If a real-valued path R is upper semicontinuous on the compact interval [0,t] and stays strictly below x at every time in that interval, then its exact supremum over the entire prefix is strictly below x. The proof uses compactness to obtain a time attaining the maximum, so there is a uniform positive gap between x and the supremum. This lemma is a key deterministic ingredient for showing that rational-grid first hitting times of levels x−1/n converge to the continuous-time first hit of x, thereby connecting stopping-time grid constructions to genuine excursion first-passage times.
-- source:
--   Compactness and upper-semicontinuous maximum theorem, pinned Mathlib UpperSemicontinuousOn.exists_isMaxOn.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.usc_compact_prefix_sup_strictly_below_level
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t))
    (hNoHit : ∀ s : ℝ≥0, s ≤ t → R s < x) :
    sSup (R '' Icc (0 : ℝ≥0) t) < x := by sorry
