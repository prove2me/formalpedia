-- Prove2me | solution 1 for exists_tendsto_div_of_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:05.315644+00:00
-- url     : https://prove2.me/submissions/5a60fa17-c97e-4363-a60b-4e2d9c59e63c

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
public import Theorems.Thm_exists_tendsto_div_of_le_add_const
section
@[expose] public section
open Filter
open scoped Topology
private theorem bddBelow_div_of_mul_le {u : ℕ → ℝ} {b : ℝ} (h : ∀ n, 0 < n → n * b ≤ u n) :
    BddBelow (Set.range fun n : ℕ ↦ u n / n) := by
  refine ⟨min b 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]
  linarith [h n hn, mul_le_mul_of_nonneg_right (min_le_left b 0) (Nat.cast_nonneg n)]
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
theorem _root_.solution {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ m n, |u (m + n) - u m - u n| ≤ C) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, |u n - n * L| ≤ C := by
  have hup : ∀ m n, u (m + n) ≤ u m + u n + C := fun m n ↦ by linarith [(abs_le.1 (h m n)).2]
  have hlo : ∀ m n, -u (m + n) ≤ -u m + -u n + C := fun m n ↦ by
    linarith [(abs_le.1 (h m n)).1]
  -- `n * (u 1 - C) ≤ u n ≤ n * (u 1 + C)` for `n ≥ 1`, so `u n / n` is bounded
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0 0)
  have hlin : ∀ n, 0 < n → n * (u 1 - C) ≤ u n ∧ n * -(u 1 + C) ≤ -u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => constructor <;> simp <;> linarith
    | succ n hn ih => push_cast; constructor <;> linarith [ih.1, ih.2, hup n 1, hlo n 1]
  obtain ⟨L, hL, hLu⟩ :=
    exists_tendsto_div_of_le_add_const hup (bddBelow_div_of_mul_le fun n hn ↦ (hlin n hn).1)
  obtain ⟨L', hL', hLu'⟩ :=
    exists_tendsto_div_of_le_add_const hlo (bddBelow_div_of_mul_le fun n hn ↦ (hlin n hn).2)
  obtain rfl : L' = -L := tendsto_nhds_unique hL' (by simpa [neg_div] using hL.neg)
  exact ⟨L, hL, fun n ↦ abs_le.2 ⟨by linarith [hLu n], by linarith [hLu' n, mul_neg (n : ℝ) L]⟩⟩
