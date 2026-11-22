-- Prove2me | solution 28 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:50.539987+00:00
-- url     : https://prove2.me/submissions/f12ac26d-df37-48fc-89e2-81b227e6bcf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_sharp_mobius_character_power_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

theorem solution : RiemannHypothesis := by
  intro s hz htriv hone
  have : Subsingleton (ZMod 1) := inferInstanceAs (Subsingleton (Fin 1))
  have hsum : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1),
          (1 : DirichletCharacter ℂ 1) (k : ZMod 1) * (ArithmeticFunction.moebius k : ℂ) =
        ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ) := by
    intro n
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp
    · intro k _
      rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
  have key : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → 1 - σ ≤ s.re ∧ s.re ≤ σ := by
    intro σ h1 h2
    have h := (GRH.sharp_mobius_character_power_bound 1 (1 : DirichletCharacter ℂ 1) σ h1 h2).congr_left
      hsum
    exact nontrivial_zero_strip_of_moebius_summatory_power_bound (r := σ) (by linarith) h hz htriv hone
  have h34 := key (3 / 4) (by norm_num) (by norm_num)
  have hle : s.re ≤ 1 / 2 := by
    by_contra hlt
    push_neg at hlt
    have := (key ((1 / 2 + s.re) / 2) (by linarith) (by linarith [h34.2])).2
    linarith
  have hge : 1 / 2 ≤ s.re := by
    by_contra hlt
    push_neg at hlt
    have := (key (1 - (s.re + 1 / 2) / 2) (by linarith [h34.1]) (by linarith [h34.1])).1
    linarith
  exact le_antisymm hle hge
