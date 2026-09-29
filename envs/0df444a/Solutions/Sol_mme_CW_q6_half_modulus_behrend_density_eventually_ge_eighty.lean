-- Prove2me | solution 1 for mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:19:12.653644+00:00
-- url     : https://prove2.me/submissions/becb5f83-fa8f-4c88-9733-bb91459081e0

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt

open Filter Topology

private theorem self_le_choose_of_pos_of_lt :
    ∀ {n k : ℕ}, 0 < k → k < n → n ≤ Nat.choose n k := by
  intro n
  induction n with
  | zero =>
      intro k hk hkn
      omega
  | succ n ih =>
      intro k hk hkn
      cases k with
      | zero => simp at hk
      | succ k =>
          by_cases hk0 : k = 0
          · subst k
            simp
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have hkle : k < n := by omega
            have hchoose : n ≤ Nat.choose n k := ih hkpos hkle
            have hpositive : 0 < Nat.choose n (k + 1) :=
              Nat.choose_pos (by omega)
            have hpositive' : 1 ≤ Nat.choose n k.succ := by
              exact hpositive
            rw [Nat.choose_succ_succ]
            exact (Nat.succ_le_succ hchoose).trans
              (Nat.add_le_add_left hpositive' _)

private theorem behrend_density_tendsto_atTop :
    Tendsto
      (fun x : ℝ => x * Real.exp (-4 * Real.sqrt (Real.log x)))
      atTop atTop := by
  have hpoly : Tendsto (fun y : ℝ => y ^ 2 - 4 * y) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const
        (by norm_num : (0 : ℝ) < 2))
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with y hy
    nlinarith [sq_nonneg (y - 8)]
  have hy : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hmain := Real.tendsto_exp_atTop.comp (hpoly.comp hy)
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  change
    Real.exp ((Real.sqrt (Real.log x)) ^ 2 -
        4 * Real.sqrt (Real.log x)) =
      x * Real.exp (-4 * Real.sqrt (Real.log x))
  conv_rhs =>
    enter [1]
    rw [← Real.exp_log hxpos]
  rw [← Real.exp_add, Real.sq_sqrt hlog]
  congr 1 <;> ring

theorem solution :
    ∀ᶠ N : ℕ in atTop,
      ∀ G : ℕ, 0 < G → G < N →
        let X : ℕ := Nat.choose N G
        let Q : ℕ := (4 * X ^ 2 + 1) / 2
        (80 : ℝ) ≤
          (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) := by
  have hdensity : ∀ᶠ x : ℝ in atTop,
      (80 : ℝ) ≤ x * Real.exp (-4 * Real.sqrt (Real.log x)) :=
    behrend_density_tendsto_atTop.eventually (eventually_ge_atTop 80)
  obtain ⟨x0, hx0⟩ := (eventually_atTop.1 hdensity)
  have hN : ∀ᶠ N : ℕ in atTop, x0 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x0)
  filter_upwards [hN, eventually_ge_atTop (1 : ℕ)] with N hNx0 hN1
  intro G hG hGN
  dsimp only
  let X : ℕ := Nat.choose N G
  have hNX : N ≤ X := self_le_choose_of_pos_of_lt hG hGN
  have hX1 : 1 ≤ X := hN1.trans hNX
  have hNQ : N ≤ (4 * X ^ 2 + 1) / 2 := by
    have hformula : (4 * X ^ 2 + 1) / 2 = 2 * X ^ 2 := by omega
    rw [hformula]
    nlinarith
  apply hx0
  exact hNx0.trans (by exact_mod_cast hNQ)
