-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_compact_sup_level_hit_before_lower_endpoint
-- name    : AvramDividend.Classical.usc_compact_sup_level_hit_before_lower_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:41:26.840275+00:00
-- url     : https://prove2.me/theorems/d09ec767-49b5-45d7-a346-a14e9bcc7ff1
-- title:
--   A compact upper-semicontinuous path attaining a supremum strictly above its endpoint reaches that maximum before the endpoint
-- statement:
--   Let R be any upper-semicontinuous real path on a compact nonnegative-time interval [0,H]. If its true mathematical supremum over the interval is x and R(H)<x, then R reaches exactly x at a time t strictly before H. This strengthens the finite-excursion maximum-attainment lemma, which required the endpoint to return to zero. It provides the general first-hitting-time geometry for proving that a genuinely downward-regular reflected Lévy process's finite-horizon running maximum cannot have a positive atom on the event its terminal reflected value lies below the maximum. By the maximum principle on compact upper-semicontinuous functions, select a maximizer; its value equals the supremum; its time cannot be H.
-- source:
--   Pinned Mathlib UpperSemicontinuousOn.exists_isMaxOn, isCompact_Icc, csSup_le and le_csSup.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.usc_compact_sup_level_hit_before_lower_endpoint
    (R : ℝ≥0 → ℝ) (H : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 H))
    (hSup : sSup (R '' Icc 0 H) = x)
    (hEnd : R H < x) :
    ∃ t : ℝ≥0, t < H ∧ R t = x := by sorry
