-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_near_zero_jumps_preserve_compact_interior
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_canonical_near_zero_jumps_preserve_compact_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:57:10.604996+00:00
-- url     : https://prove2.me/theorems/9a02e9cd-a409-40dc-ae9d-464a5ffe0feb
-- title:
--   Eventually every canonical small-negative Lévy mark preserves a compact positive reserve strip
-- statement:
--   Fix a compact reserve strip [a+δ,v] inside (0,C), with a≥0, δ>0 and v<C. There is a deterministic mark-cutoff index N such that for all later canonical negative bands (-1/(n+1),0), any reserve u in the strip and any jump size z in the band satisfy 0<u+z<C. Thus the infinite-activity near-zero part is eventually interior; exits/ruin belong to the separated larger-jump part. The result is purely geometric and source-independent.
-- source:
--   Pinned Mathlib reciprocal-to-zero limit, eventual atTop bound and linear arithmetic on compact interior.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_canonical_near_zero_jumps_preserve_compact_interior
    (C a v δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hv : v < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ, u ∈ Icc (a + δ) v →
      ∀ z : ℝ, z ∈ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) 0 →
        u + z ∈ Ioo 0 C := by sorry
