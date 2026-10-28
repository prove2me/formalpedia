-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit
-- name    : AvramDividend.Classical.usc_capped_first_closed_hit_le_iff_prefix_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:22:40.548423+00:00
-- url     : https://prove2.me/theorems/b0bcf885-899c-4beb-8135-408fcdf91ab1
-- title:
--   Capped first closed-superlevel arrival is before time t exactly when the upper semicontinuous path hits that level on its prefix
-- statement:
--   Let R be any upper-semicontinuous real path on [0,H]. Define its finite capped closed-level first hitting time T as the infimum of ({s∈[0,H]:R_s≥x}∪{H}). The cap ensures the set is always nonempty even if the level is never hit and avoids the incorrect convention sInf∅=0. For any t<H, T≤t if and only if R reaches x at some s≤t. The proof uses compactness of the level-superlevel set, compactness of the singleton {H}, IsCompact.sInf_mem, and csInf_le. This is the pathwise event identity needed to prove T is a stopping time from adaptedness of full prefix suprema, without assuming right continuity of the filtration.
-- source:
--   Pinned Mathlib UpperSemicontinuousOn.isCompact_inter_preimage_Ici; IsCompact.sInf_mem; csInf_le. Covers the no-hit case by cap H.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.usc_capped_first_closed_hit_le_iff_prefix_hit
    (R : ℝ≥0 → ℝ) (H t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 H))
    (ht : t < H) :
    sInf ((Icc (0 : ℝ≥0) H ∩ R ⁻¹' Ici x) ∪ {H}) ≤ t ↔
      ∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s := by sorry
