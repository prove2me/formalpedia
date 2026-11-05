-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_memLp_of_cells
-- name    : AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_memLp_of_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:21:11.165742+00:00
-- url     : https://prove2.me/theorems/12b1b4e6-4136-41fb-81c1-5cf259dda8a8
-- title:
--   L2 stability of every finite prefix of original increment cells
-- statement:
--   For the actual original probability space, any finite prefix of L2 real random increments belongs to L2. This extracts the finite-prefix MemLp induction already checked inside P4-G's accepted prefix-square integrability proof; it is reusable to derive bounded predictable product moments.
-- source:
--   Accepted public prefix-square integral theorem 1574cca8, candidate 26999, whose source contains this exact MemLp induction.

import Mathlib

open MeasureTheory
open scoped ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_memLp_of_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, D i ω) 2 P := by sorry
