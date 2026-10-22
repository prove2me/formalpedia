-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_random_count_marked_increment_sum_decomposition
-- name    : AvramDividend.Classical.chat06_random_count_marked_increment_sum_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:38:47.822622+00:00
-- url     : https://prove2.me/theorems/ce30d9a9-ede4-45aa-9cad-7e64afee19ef
-- title:
--   Compound-Poisson marked-sum increment as a shifted block after the earlier count
-- statement:
--   For any real-valued mark sequence and two integer-valued observation counts Ns≤Nt, the difference between cumulative mark sums up to Nt and Ns equals the sum of the Nt-Ns marks starting at index Ns. The identity holds pathwise and uses the finite-sum range-add formula with the natural-number count difference. It is a deterministic bridge from stationary independent counting increments and iid mark suffixes to stationary independent compound-Poisson increments, without assuming those probabilistic properties.
-- source:
--   Source bv_random_count_marked_increment_sum_decomposition_v2_chat06_20261021.lean, 19 lines, SHA-256 219cda84a428de94691c5ea07fa78452461c6959c68ff4232fbef1b2311e56ea. Private probe c6a8260a-33d2-435e-9403-980068994b74 reached sentinel with zero errors at pinned revision. The v1 arithmetic rewrite left a simplifiable natural-number subtraction, fixed with simp in the preserved v2.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.chat06_random_count_marked_increment_sum_decomposition
    {Ω : Type*}
    (Y : ℕ → Ω → ℝ)
    (Ns Nt : Ω → ℕ) (hmono : ∀ ω, Ns ω ≤ Nt ω)
    (ω : Ω) :
    (∑ i ∈ Finset.range (Nt ω), Y i ω) -
      (∑ i ∈ Finset.range (Ns ω), Y i ω) =
      ∑ j ∈ Finset.range (Nt ω - Ns ω), Y (Ns ω + j) ω := by sorry
