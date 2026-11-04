-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:46:12.288241+00:00
-- url     : https://prove2.me/theorems/bba53a00-5bed-467e-9a24-3f76881a4268
-- title:
--   Local interior BV negative-source-jump increment has a first-order envelope
-- statement:
--   A local first-order envelope for the signed nonlinear increment w(u+z)-w(u) at a negative jump mark z with -δ≤z≤0. The source reserve u stays inside [a+δ,b], so u and the post-source state u+z both remain in the single compact interval [a,b]. A local Lipschitz certificate of constant K on that compact interval yields |increment|≤K|z|. This does not impose any global negative-tail first moment, and it is the deterministic envelope needed to control localised finite-variation small-jump compensation in the original process.
-- source:
--   Mathlib LipschitzOnWith.norm_sub_le and deterministic BV local C1 jump envelope

import Mathlib
open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound (w : ℝ → ℝ) (K : ℝ≥0) (a b δ u z : ℝ) (hδ : 0 ≤ δ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + δ) b) (hz : z ∈ Icc (-δ) 0) : |w (u + z) - w u| ≤ (K : ℝ) * |z| := by sorry
