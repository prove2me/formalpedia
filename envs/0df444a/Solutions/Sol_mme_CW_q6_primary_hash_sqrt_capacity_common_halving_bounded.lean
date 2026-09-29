-- Prove2me | solution 1 for mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:00:10.889382+00:00
-- url     : https://prove2.me/submissions/4bf89e67-31d8-41ba-984f-e500f2df2545

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
import Theorems.Thm_mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
import Theorems.Thm_mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        let N : ℕ := 2 * n
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N L G A H,
            ∃ _halving : family.CommonBalancedXYHalving,
              H ≤ 4 ^ N ∧
              raw ^ (2 * N) *
                  Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
                (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                  ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  obtain ⟨C0, hC0, hrate⟩ :=
    mme_CW_q6_primary_hash_sqrt_capacity_bounded tau htau
  let Cpoly : ℝ := 128 * ((40 : ℕ).factorial : ℝ)
  have hCpoly : 0 ≤ Cpoly := by
    dsimp [Cpoly]
    positivity
  have htend : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop
        (by norm_num : 0 < 2))
  have heven := htend.eventually hrate
  refine ⟨C0 + Cpoly, by positivity, ?_⟩
  filter_upwards [heven] with n hn
  dsimp only at hn ⊢
  let N : ℕ := 2 * n
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  have hn' :
      ∃ A H : ℕ,
        ∃ family : CWQ6PrimaryHashFamily N L G A H,
          H ≤ 4 ^ N ∧
          raw ^ (2 * N) *
              Real.exp (-C0 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
              ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
    simpa only [N, lambda, L, G, side, raw] using hn
  obtain ⟨A, H, family, hHcap, hrateN⟩ := hn'
  have hlambdaNonneg : 0 ≤ lambda * (N : ℝ) := by
    dsimp [lambda]
    positivity
  have hfloorLe : (L : ℝ) ≤ lambda * (N : ℝ) := by
    dsimp [L]
    exact Nat.floor_le hlambdaNonneg
  have hlambdaOne : lambda ≤ 1 := by
    dsimp [lambda]
    apply (div_le_one (by positivity)).2
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (3 * tau)]
  have hLle : L ≤ N := by
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hmul : lambda * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith
    exact_mod_cast hfloorLe.trans hmul
  have hLG : L + G = 2 * n := by
    dsimp [G, N]
    omega
  have hlhsPos : 0 < raw ^ (2 * N) *
      Real.exp (-C0 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
    apply mul_pos
    · apply pow_pos
      dsimp [raw]
      positivity
    · exact Real.exp_pos _
  have hApos : 0 < A := by
    by_contra hA
    have hA0 : A = 0 := Nat.eq_zero_of_not_pos hA
    have hzero :
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau) = 0 := by
      simp [hA0]
    rw [hzero] at hrateN
    exact (not_lt_of_ge hrateN) hlhsPos
  obtain ⟨A', H', subfamily, _hA', _hH', hH'cap,
      ⟨halving⟩, hextract⟩ :=
    mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
      hLG family hApos hHcap
  refine ⟨A', H', subfamily, halving, hH'cap, ?_⟩
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let P : ℕ := 128 * (N + 1) ^ 20
  let oldCap : ℝ := (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2)
  let newCap : ℝ := (((A' ^ 3 : ℕ) : ℝ) * (H' : ℝ) ^ 2)
  let sideTau : ℝ := ((((side * side * side : ℕ) : ℝ)) ^ tau)
  have hextractR : oldCap ≤ (P : ℝ) * newCap := by
    dsimp [oldCap, P, newCap]
    exact_mod_cast hextract
  have hpoly : (P : ℝ) ≤ Real.exp (Cpoly * x) := by
    simpa only [P, Cpoly, x] using
      mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt N
  have hkill : (P : ℝ) * Real.exp (-Cpoly * x) ≤ 1 := by
    calc
      (P : ℝ) * Real.exp (-Cpoly * x) ≤
          Real.exp (Cpoly * x) * Real.exp (-Cpoly * x) := by
        gcongr
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
  have hsideNonneg : 0 ≤ sideTau := by
    dsimp [sideTau]
    positivity
  change raw ^ (2 * N) * Real.exp (-(C0 + Cpoly) * x) ≤
    newCap * sideTau
  calc
    raw ^ (2 * N) * Real.exp (-(C0 + Cpoly) * x) =
        (raw ^ (2 * N) * Real.exp (-C0 * x)) *
          Real.exp (-Cpoly * x) := by
      rw [show -(C0 + Cpoly) * x = (-C0 * x) + (-Cpoly * x) by ring,
        Real.exp_add]
      ring
    _ ≤ (oldCap * sideTau) * Real.exp (-Cpoly * x) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [oldCap, sideTau, x] using hrateN)
        (Real.exp_pos _).le
    _ ≤ (((P : ℝ) * newCap) * sideTau) *
        Real.exp (-Cpoly * x) := by
      gcongr
    _ = (newCap * sideTau) *
        ((P : ℝ) * Real.exp (-Cpoly * x)) := by ring
    _ ≤ (newCap * sideTau) * 1 := by
      exact mul_le_mul_of_nonneg_left hkill (mul_nonneg (by positivity) hsideNonneg)
    _ = newCap * sideTau := by ring
