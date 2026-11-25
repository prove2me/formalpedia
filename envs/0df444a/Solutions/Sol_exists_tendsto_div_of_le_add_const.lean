-- Prove2me | solution 1 for exists_tendsto_div_of_le_add_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:25:33.154674+00:00
-- url     : https://prove2.me/submissions/6c360101-85f4-4158-99bb-81a259aa833c

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
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
    (h : ∀ m n, u (m + n) ≤ u m + u n + C) (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, n * L - C ≤ u n := by
  have hs : Subadditive fun n ↦ u n + C := fun m n ↦ by linarith [h m n]
  have hbdd' : BddBelow (Set.range fun n : ℕ ↦ (u n + C) / n) := by
    obtain ⟨b, hb⟩ := hbdd
    refine bddBelow_div_of_mul_le (b := b - |C|) fun n hn ↦ ?_
    have := (le_div_iff₀ (Nat.cast_pos.2 hn)).1 (hb ⟨n, rfl⟩)
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [le_mul_of_one_le_left (abs_nonneg C) h1, neg_abs_le C]
  refine ⟨hs.lim, ?_, fun n ↦ ?_⟩
  · refine ((hs.tendsto_lim hbdd').sub (tendsto_const_div_atTop_nhds_zero_nat C)).congr' ?_
      |>.trans (by rw [sub_zero])
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [add_div, add_sub_cancel_right]
  · rcases n.eq_zero_or_pos with rfl | hn
    · simpa using (show -C ≤ u 0 by linarith [h 0 0])
    have := (le_div_iff₀ (Nat.cast_pos.2 hn)).1 (hs.lim_le_div hbdd' hn.ne')
    linarith
