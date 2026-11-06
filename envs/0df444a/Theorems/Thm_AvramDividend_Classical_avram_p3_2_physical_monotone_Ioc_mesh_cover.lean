-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_monotone_Ioc_mesh_cover
-- name    : AvramDividend.Classical.avram_p3_2_physical_monotone_Ioc_mesh_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:50:18.251699+00:00
-- url     : https://prove2.me/theorems/761f6a1e-413a-4196-b682-fe2a03705cca
-- title:
--   Finite monotone physical stopped-grid half-open cells cover the whole terminal interval
-- statement:
--   For any nondecreasing real time grid u, the union of the first n half-open Ioc adjacent time cells is exactly Ioc (u 0) (u n), including possibly repeated stopped points.
-- source:
--   Induction on n with endpoint monotonicity and split at the nth grid endpoint; a pure finite interval cover needed to turn original physical stopped Stieltjes cell sums into a whole-horizon integral.

import Mathlib

open Set

theorem AvramDividend.Classical.avram_p3_2_physical_monotone_Ioc_mesh_cover
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) =
      Ioc (u 0) (u n):= by sorry
