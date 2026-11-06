-- Prove2me | solution 1 for summable_iff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:01:32.671089+00:00
-- url     : https://prove2.me/submissions/60867142-357a-432f-ba6e-ee1b2b623978

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SumIntegralComparisons

open Filter Asymptotics

theorem solution {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun i _ => hu i
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro h <;> rcases h with ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1
