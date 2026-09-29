-- Prove2me | solution 1 for cyclotomic_velu_xLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/cb175b42-cf21-5f06-b8db-e07aa297fcdc

import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_cyclotomic_velu_xLaw

set_option autoImplicit false

open Finset Polynomial

section Aux4

private lemma xdiff {F : Type*} [Field F] {a b : F} (ha : a ≠ 1) (hb : b ≠ 1) :
    a / (1 - a) ^ 2 - b / (1 - b) ^ 2
      = (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
  have ha' : (1 : F) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hb' : (1 : F) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  field_simp
  ring

private lemma principal_eq {F : Type*} [Field F] {t u r d : F} (hd : d ≠ 0)
    (h : t * d + u = r * d ^ 2) : t / d + u / d ^ 2 = r := by
  field_simp
  linear_combination h

private lemma perk {F : Type*} [Field F] {a b b' : F} (hbb' : b * b' = 1)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a * b ≠ 1) (hne : a ≠ b) :
    b / (1 - b) ^ 2 * (1 + 6 * (b / (1 - b) ^ 2)) / (a / (1 - a) ^ 2 - b / (1 - b) ^ 2)
      + (b / (1 - b) ^ 2) ^ 2 * (1 + 4 * (b / (1 - b) ^ 2))
          / (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
    = a * b / (1 - a * b) ^ 2 + a * b' / (1 - a * b') ^ 2 - 2 * (b / (1 - b) ^ 2) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hbb'
  have hb' : b' = b⁻¹ := eq_inv_of_mul_eq_one_right hbb'
  subst hb'
  have ha' : (1 : F) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hb1' : (1 : F) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hab' : (1 : F) - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hamb : a - b ≠ 0 := sub_ne_zero.mpr hne
  have habi0 : (1 : F) - a * b⁻¹ ≠ 0 := by
    have h1 : a * b⁻¹ ≠ 1 := fun h => hne ((mul_inv_eq_one₀ hb0).mp h)
    exact sub_ne_zero.mpr (Ne.symm h1)
  have hAB : a / (1 - a) ^ 2 - b / (1 - b) ^ 2
      = (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := xdiff ha hb
  have hABne : a / (1 - a) ^ 2 - b / (1 - b) ^ 2 ≠ 0 := by
    rw [hAB]
    exact div_ne_zero (mul_ne_zero hamb hab')
      (mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ hb1'))
  have habi : a * b⁻¹ / (1 - a * b⁻¹) ^ 2 = a * b / (b - a) ^ 2 := by
    rw [div_eq_div_iff (pow_ne_zero _ habi0) (pow_ne_zero _ hba)]
    field_simp
  rw [habi]
  apply principal_eq hABne
  have hDq : ((1 - a) ^ 2 * (1 - b) ^ 2 : F) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ hb1')
  have h1 : a * b / (1 - a * b) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
      = a * b * (a - b) ^ 2 / ((1 - a) ^ 2 * (1 - b) ^ 2) ^ 2 := by
    rw [hAB, div_pow, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hab') (pow_ne_zero _ hDq))
        (pow_ne_zero _ hDq)]
    ring
  have h2 : a * b / (b - a) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
      = a * b * (1 - a * b) ^ 2 / ((1 - a) ^ 2 * (1 - b) ^ 2) ^ 2 := by
    rw [hAB, div_pow, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hba) (pow_ne_zero _ hDq))
        (pow_ne_zero _ hDq)]
    ring
  have h3 : b / (1 - b) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
      = b * (a - b) ^ 2 * (1 - a * b) ^ 2
          / ((1 - b) ^ 2 * ((1 - a) ^ 2 * (1 - b) ^ 2) ^ 2) := by
    rw [hAB, div_pow, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hb1') (pow_ne_zero _ hDq))
        (mul_ne_zero (pow_ne_zero _ hb1') (pow_ne_zero _ hDq))]
    ring
  have expand : (a * b / (1 - a * b) ^ 2 + a * b / (b - a) ^ 2 - 2 * (b / (1 - b) ^ 2))
        * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
      = a * b / (1 - a * b) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
        + a * b / (b - a) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2
        - 2 * (b / (1 - b) ^ 2 * (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) ^ 2) := by
    ring
  rw [expand, h1, h2, h3, hAB]
  field_simp
  ring

private lemma x_inv {F : Type*} [Field F] {v : F} (hv : v ≠ 0) :
    v⁻¹ / (1 - v⁻¹) ^ 2 = v / (1 - v) ^ 2 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 : F) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have hvi : v⁻¹ ≠ 1 := fun h => hv1 (by rw [← inv_inv v, h, inv_one])
    have h2 : (1 : F) - v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm hvi)
    rw [div_eq_div_iff (pow_ne_zero _ h2) (pow_ne_zero _ h1)]
    field_simp
    ring

private lemma perk_at {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {X w : F} (hw1 : w ≠ 1) (hXw : X = w / (1 - w) ^ 2)
    (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 (p / 2)) :
    ζ ^ k / (1 - ζ ^ k) ^ 2 * (1 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2)) / (X - ζ ^ k / (1 - ζ ^ k) ^ 2)
      + (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 * (1 + 4 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
          / (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
    = w * ζ ^ k / (1 - w * ζ ^ k) ^ 2 + w * ζ ^ (p - k) / (1 - w * ζ ^ (p - k)) ^ 2
        - 2 * (ζ ^ k / (1 - ζ ^ k) ^ 2) := by
  subst hXw
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hkp : k < p := lt_of_le_of_lt hk2 (Nat.div_lt_self hp.pos one_lt_two)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hbb' : ζ ^ k * ζ ^ (p - k) = 1 := by
    rw [← pow_add, show k + (p - k) = p by omega]
    exact hζ.pow_eq_one
  have hb : ζ ^ k ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) hkp
  have hne : w ≠ ζ ^ k := fun h => hX k hk (by rw [h])
  have hab : w * ζ ^ k ≠ 1 := by
    intro h
    apply hX k hk
    rw [eq_inv_of_mul_eq_one_left h, x_inv (pow_ne_zero _ hζ0)]
  exact perk hbb' hw1 hb hab hne

private lemma pow_ne_one_of_good {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {X w : F} (hw1 : w ≠ 1) (hXw : X = w / (1 - w) ^ 2)
    (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2) :
    w ^ p ≠ 1 := by
  intro hwp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, hjp, hj⟩ := hζ.eq_pow_of_pow_eq_one hwp
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hw1 hj.symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  by_cases hjm : j ≤ p / 2
  · exact hX j (Finset.mem_Icc.mpr ⟨by omega, hjm⟩) (by rw [hXw, ← hj])
  · have hmem : p - j ∈ Finset.Icc 1 (p / 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    apply hX (p - j) hmem
    rw [hXw, ← hj]
    have hinv : ζ ^ j = (ζ ^ (p - j))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, show j + (p - j) = p by omega]
      exact hζ.pow_eq_one
    rw [hinv, x_inv (pow_ne_zero _ hζ0)]

end Aux4

section Aux13

variable {K : Type*} [Field K] {ζ : K} {p : ℕ}

private lemma Ico_eq_union (hp : Odd p) :
    Ico 1 p = Icc 1 (p / 2) ∪ (Icc 1 (p / 2)).image (fun k => p - k) := by
  obtain ⟨m, rfl⟩ := hp
  have hm : (2 * m + 1) / 2 = m := by omega
  ext j
  simp only [mem_Ico, mem_union, mem_Icc, mem_image, hm]
  constructor
  · intro hj
    by_cases hjm : j ≤ m
    · exact Or.inl ⟨hj.1, hjm⟩
    · exact Or.inr ⟨2 * m + 1 - j, ⟨by omega, by omega⟩, by omega⟩
  · rintro (⟨h1, h2⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩) <;> omega

private lemma Icc_disjoint_image (hp : Odd p) :
    Disjoint (Icc 1 (p / 2)) ((Icc 1 (p / 2)).image (fun k => p - k)) := by
  obtain ⟨m, rfl⟩ := hp
  have hm : (2 * m + 1) / 2 = m := by omega
  rw [Finset.disjoint_left]
  intro j hj hj'
  simp only [mem_Icc, mem_image, hm] at hj hj'
  obtain ⟨k, hk, hkj⟩ := hj'
  omega

private lemma sub_injOn (p : ℕ) : Set.InjOn (fun k => p - k) ↑(Icc 1 (p / 2)) := by
  intro a ha b hb hab
  simp only [coe_Icc, Set.mem_Icc] at ha hb
  have hab' : p - a = p - b := hab
  omega

private lemma sum_Ico_fold (hp : Odd p) (f : ℕ → K) :
    ∑ j ∈ Ico 1 p, f j = ∑ k ∈ Icc 1 (p / 2), (f k + f (p - k)) := by
  rw [Ico_eq_union hp, sum_union (Icc_disjoint_image hp), sum_image (sub_injOn p),
    sum_add_distrib]

private lemma prod_Ico_fold (hp : Odd p) (f : ℕ → K) :
    ∏ j ∈ Ico 1 p, f j = ∏ k ∈ Icc 1 (p / 2), (f k * f (p - k)) := by
  rw [Ico_eq_union hp, prod_union (Icc_disjoint_image hp), prod_image (sub_injOn p),
    prod_mul_distrib]

private lemma zeta_pow_sub_mul_pow (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ≤ p) :
    ζ ^ (p - k) * ζ ^ k = 1 := by
  rw [← pow_add, Nat.sub_add_cancel hk, hζ.pow_eq_one]

private lemma x_reflect (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk : k ≤ p) :
    ζ ^ (p - k) / (1 - ζ ^ (p - k)) ^ 2 = ζ ^ k / (1 - ζ ^ k) ^ 2 := by
  have h1 := zeta_pow_sub_mul_pow hζ hk
  by_cases h0 : (1 : K) - ζ ^ k = 0
  · have hk1 : ζ ^ k = 1 := (sub_eq_zero.mp h0).symm
    have : ζ ^ (p - k) = 1 := by rwa [hk1, mul_one] at h1
    simp [this, hk1]
  · have h0' : (1 : K) - ζ ^ (p - k) ≠ 0 := by
      intro h
      apply h0
      have e : ζ ^ (p - k) = 1 := (sub_eq_zero.mp h).symm
      rw [e, one_mul] at h1
      rw [h1, sub_self]
    rw [div_eq_div_iff (pow_ne_zero 2 h0') (pow_ne_zero 2 h0)]
    linear_combination (ζ ^ k - ζ ^ (p - k)) * h1

private lemma orbit_pow_sum (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    ∑ j ∈ range p, (ζ ^ j) ^ n = if p ∣ n then (p : K) else 0 := by
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    have h1 : ∀ j ∈ range p, (ζ ^ j) ^ (p * c) = 1 := fun j _ => by
      rw [← pow_mul, mul_comm j, mul_assoc, pow_mul, hζ.pow_eq_one, one_pow]
    rw [sum_congr rfl h1, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have h1 : ζ ^ n ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd n).mp e)
    have h2 : (ζ ^ n) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    calc ∑ j ∈ range p, (ζ ^ j) ^ n = ∑ j ∈ range p, (ζ ^ n) ^ j := by
          refine sum_congr rfl fun j _ => ?_
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 0 := by
          have h3 := mul_neg_geom_sum (ζ ^ n) p
          rw [h2, sub_self] at h3
          exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm h1))

private lemma orbit_numerator (hζ : IsPrimitiveRoot ζ p) (w : K) :
    ∑ j ∈ range p, w * ζ ^ j * (∑ i ∈ range p, (w * ζ ^ j) ^ i) ^ 2
      = (p : K) ^ 2 * w ^ p := by
  have hexp : ∀ j ∈ range p, w * ζ ^ j * (∑ i ∈ range p, (w * ζ ^ j) ^ i) ^ 2
      = ∑ a ∈ range p, ∑ b ∈ range p, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1) := by
    intro j _
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [← mul_pow]
    ring
  rw [sum_congr rfl hexp, sum_comm]
  have hinner : ∀ a ∈ range p,
      ∑ j ∈ range p, ∑ b ∈ range p, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1)
        = (p : K) * w ^ p := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [sum_comm]
    have hb : ∀ b ∈ range p, ∑ j ∈ range p, (ζ ^ j) ^ (a + b + 1) * w ^ (a + b + 1)
        = if b = p - 1 - a then (p : K) * w ^ p else 0 := by
      intro b hb
      have hb' := mem_range.mp hb
      rw [← sum_mul, orbit_pow_sum hζ]
      by_cases hab : b = p - 1 - a
      · have e : a + b + 1 = p := by omega
        rw [if_pos (e ▸ dvd_refl p), if_pos hab, e]
      · have hnd : ¬ p ∣ a + b + 1 := by
          rintro ⟨c, hc⟩
          have hc1 : p * c < p * 2 := by omega
          have hc2 : 0 < p * c := by omega
          have hc3 : c < 2 := Nat.lt_of_mul_lt_mul_left hc1
          have hc4 : 0 < c := Nat.pos_of_mul_pos_left hc2
          interval_cases c
          omega
        rw [if_neg hnd, if_neg hab, zero_mul]
    rw [sum_congr rfl hb, sum_ite_eq' (range p) (p - 1 - a) (fun _ => (p : K) * w ^ p),
      if_pos (mem_range.mpr (by omega))]
  rw [sum_congr rfl hinner, sum_const, card_range, nsmul_eq_mul, sq, mul_assoc]

private lemma geom_orbit (hζ : IsPrimitiveRoot ζ p) (w : K) (j : ℕ) :
    (1 - w * ζ ^ j) * ∑ i ∈ range p, (w * ζ ^ j) ^ i = 1 - w ^ p := by
  rw [mul_neg_geom_sum, mul_pow, ← pow_mul, mul_comm j p, pow_mul, hζ.pow_eq_one, one_pow,
    mul_one]

private lemma one_sub_orbit_ne_zero (hζ : IsPrimitiveRoot ζ p) {w : K} (hw : w ^ p ≠ 1)
    (j : ℕ) : 1 - w * ζ ^ j ≠ 0 := by
  intro h0
  have hg := geom_orbit hζ w j
  rw [h0, zero_mul] at hg
  exact hw (sub_eq_zero.mp hg.symm).symm

private lemma orbit_sum_x (hζ : IsPrimitiveRoot ζ p) {w : K} (hw : w ^ p ≠ 1) :
    ∑ j ∈ range p, w * ζ ^ j / (1 - w * ζ ^ j) ^ 2
      = (p : K) ^ 2 * w ^ p / (1 - w ^ p) ^ 2 := by
  have hD : (1 : K) - w ^ p ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hterm : ∀ j ∈ range p, w * ζ ^ j / (1 - w * ζ ^ j) ^ 2
      = w * ζ ^ j * (∑ i ∈ range p, (w * ζ ^ j) ^ i) ^ 2 / (1 - w ^ p) ^ 2 := by
    intro j _
    have hg := geom_orbit hζ w j
    have hv := one_sub_orbit_ne_zero hζ hw j
    rw [div_eq_div_iff (pow_ne_zero 2 hv) (pow_ne_zero 2 hD), ← hg]
    ring
  rw [sum_congr rfl hterm]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, orbit_numerator hζ w]

private lemma prod_range_sub (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (w t : K) :
    ∏ j ∈ range p, (t - w * ζ ^ j) = t ^ p - w ^ p := by
  have h := congrArg (eval t) (X_pow_sub_C_eq_prod hζ hp (rfl : w ^ p = w ^ p))
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
  rw [h]
  exact prod_congr rfl fun j _ => by rw [mul_comm]

private lemma prod_Ico_X_sub_C (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) :
    ∏ j ∈ Ico 1 p, (X - C (ζ ^ j)) = ∑ i ∈ range p, (X : K[X]) ^ i := by
  have h := X_pow_sub_C_eq_prod hζ hp (one_pow p : (1 : K) ^ p = 1)
  have hsplit : ∏ i ∈ range p, (X - C (ζ ^ i * 1)) = (X - 1) * ∏ j ∈ Ico 1 p, (X - C (ζ ^ j)) := by
    rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot hp]
    simp only [mul_one, pow_zero, C_1]
  have hX1 : (X - 1 : K[X]) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : K)
  apply mul_left_cancel₀ hX1
  rw [← hsplit, ← h, C_1, mul_geom_sum]

private lemma prod_Ico_sub (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (w : K) :
    ∏ j ∈ Ico 1 p, (w - ζ ^ j) = ∑ i ∈ range p, w ^ i := by
  have h := congrArg (eval w) (prod_Ico_X_sub_C hζ hp)
  simpa only [eval_prod, eval_sub, eval_X, eval_C, eval_geom_sum] using h

private lemma prod_Ico_one_sub_pow (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) :
    ∏ j ∈ Ico 1 p, (1 - ζ ^ j) = (p : K) := by
  have h := prod_Ico_sub hζ hp 1
  simpa only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] using h

private lemma prod_Ico_one_sub (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (w : K) :
    ∏ j ∈ Ico 1 p, (1 - w * ζ ^ j) = ∑ i ∈ range p, w ^ i := by
  by_cases hw : w = 1
  · subst hw
    simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact prod_Ico_one_sub_pow hζ hp
  · have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    apply mul_left_cancel₀ h1
    have h := prod_range_sub hζ hp w 1
    rw [Finset.prod_range_eq_mul_Ico _ hp, pow_zero, mul_one, one_pow] at h
    rw [h, mul_neg_geom_sum]

private lemma one_sub_mul_geom (w : K) (p : ℕ) :
    (1 - w) * ∑ i ∈ range p, w ^ i = 1 - w ^ p := mul_neg_geom_sum w p

private lemma X_sub_one_mul_Phi (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) :
    (X - 1 : K[X]) * ∏ j ∈ Ico 1 p, (X - C (ζ ^ j)) = X ^ p - 1 := by
  rw [prod_Ico_X_sub_C hζ hp, mul_geom_sum]

private lemma one_sub_pow_ne_zero (hζ : IsPrimitiveRoot ζ p) {j : ℕ} (hj : j ∈ Ico 1 p) :
    (1 : K) - ζ ^ j ≠ 0 := by
  rw [mem_Ico] at hj
  have h := hζ.pow_ne_one_of_pos_of_lt (by omega) hj.2
  exact sub_ne_zero.mpr (Ne.symm h)

private lemma Phi_derivs (hζ : IsPrimitiveRoot ζ p) (hp : 3 ≤ p) :
    eval 1 (∏ j ∈ Ico 1 p, (X - C (ζ ^ j))) = (p : K) ∧
    2 * eval 1 (derivative (∏ j ∈ Ico 1 p, (X - C (ζ ^ j)))) = (p : K) * (p - 1) ∧
    3 * eval 1 (derivative (derivative (∏ j ∈ Ico 1 p, (X - C (ζ ^ j)))))
      = (p : K) * (p - 1) * (p - 2) := by
  have hp0 : 0 < p := by omega
  set Φ : K[X] := ∏ j ∈ Ico 1 p, (X - C (ζ ^ j)) with hΦ
  have h0 := X_sub_one_mul_Phi hζ hp0
  rw [← hΦ] at h0

  have h1 : Φ + (X - 1) * derivative Φ = C (p : K) * X ^ (p - 1) := by
    have := congrArg derivative h0
    simpa only [derivative_mul, derivative_sub, derivative_X, derivative_one, sub_zero, one_mul,
      derivative_X_pow] using this

  have h2 : 2 * derivative Φ + (X - 1) * derivative (derivative Φ)
      = C (p : K) * (C ((p - 1 : ℕ) : K) * X ^ (p - 1 - 1)) := by
    have := congrArg derivative h1
    simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
      sub_zero, one_mul, derivative_C, zero_mul, zero_add, derivative_X_pow] at this
    linear_combination this

  have h3 : 3 * derivative (derivative Φ) + (X - 1) * derivative (derivative (derivative Φ))
      = C (p : K) * (C ((p - 1 : ℕ) : K) * (C ((p - 1 - 1 : ℕ) : K) * X ^ (p - 1 - 1 - 1))) := by
    have := congrArg derivative h2
    simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
      sub_zero, one_mul, derivative_C, derivative_X_pow, derivative_ofNat, zero_mul,
      zero_add] at this
    linear_combination this
  have e0 := congrArg (eval 1) h0
  have e1 := congrArg (eval 1) h2
  have e2 := congrArg (eval 1) h3
  simp only [eval_mul, eval_sub, eval_X, eval_one, sub_self, zero_mul, add_zero, eval_add,
    eval_C, eval_pow, one_pow, mul_one, eval_ofNat] at e0 e1 e2
  have hc1 : ((p - 1 : ℕ) : K) = (p : K) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hc2 : ((p - 1 - 1 : ℕ) : K) = (p : K) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]; ring
  refine ⟨?_, ?_, ?_⟩
  ·
    have := congrArg (eval 1) h1
    simpa [eval_mul, eval_sub, eval_X, eval_one, eval_add, eval_C, eval_pow] using this
  · rw [e1, hc1]
  · rw [e2, hc1, hc2]; ring

private lemma sum_Ico_x [CharZero K] (hζ : IsPrimitiveRoot ζ p) (hp : 3 ≤ p) :
    ∑ j ∈ Ico 1 p, ζ ^ j / (1 - ζ ^ j) ^ 2 = -((p : K) ^ 2 - 1) / 12 := by
  classical
  have hp0 : 0 < p := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  set s := Ico 1 p with hs
  set d : ℕ → K := fun j => 1 - ζ ^ j with hd
  have hdnz : ∀ j ∈ s, d j ≠ 0 := fun j hj => one_sub_pow_ne_zero hζ hj
  set Φ : K[X] := ∏ j ∈ s, (X - C (ζ ^ j)) with hΦ
  obtain ⟨hP, ha, hb⟩ := Phi_derivs hζ hp
  rw [← hs, ← hΦ] at hP ha hb

  have hPprod : eval 1 Φ = ∏ j ∈ s, d j := by
    simp only [hΦ, eval_prod, eval_sub, eval_X, eval_C, hd]
  set P := eval 1 Φ with hPdef
  have hPnz : P ≠ 0 := by rw [hP]; exact hpK

  have hΦ' : derivative Φ = ∑ b ∈ s, ∏ a ∈ s.erase b, (X - C (ζ ^ a)) := by
    rw [hΦ, derivative_prod_finset]
    refine sum_congr rfl fun b _ => ?_
    rw [derivative_X_sub_C, mul_one]
  have hΦ'' : derivative (derivative Φ)
      = ∑ b ∈ s, ∑ c ∈ s.erase b, ∏ a ∈ (s.erase b).erase c, (X - C (ζ ^ a)) := by
    rw [hΦ', derivative_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [derivative_prod_finset]
    refine sum_congr rfl fun c _ => ?_
    rw [derivative_X_sub_C, mul_one]

  have herase : ∀ b ∈ s, ∏ a ∈ s.erase b, d a = P / d b := by
    intro b hb
    rw [eq_div_iff (hdnz b hb), hPprod, mul_comm]
    exact mul_prod_erase s d hb
  have herase2 : ∀ b ∈ s, ∀ c ∈ s.erase b, ∏ a ∈ (s.erase b).erase c, d a = P / (d b * d c) := by
    intro b hb c hc
    have hc' : c ∈ s := mem_of_mem_erase hc
    rw [eq_div_iff (mul_ne_zero (hdnz b hb) (hdnz c hc')), hPprod]
    calc (∏ a ∈ (s.erase b).erase c, d a) * (d b * d c)
        = d b * (d c * ∏ a ∈ (s.erase b).erase c, d a) := by ring
      _ = d b * ∏ a ∈ s.erase b, d a := by rw [mul_prod_erase (s.erase b) d hc]
      _ = ∏ a ∈ s, d a := mul_prod_erase s d hb
  set S1 := ∑ j ∈ s, 1 / d j with hS1
  set S2 := ∑ j ∈ s, 1 / d j ^ 2 with hS2
  have hA : eval 1 (derivative Φ) = P * S1 := by
    rw [hΦ', eval_finsetSum, hS1, mul_sum]
    refine sum_congr rfl fun b hb => ?_
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    rw [herase b hb]
    ring
  have hB : eval 1 (derivative (derivative Φ)) = P * (S1 * S1 - S2) := by
    rw [hΦ'', eval_finsetSum]
    have : ∀ b ∈ s, eval 1 (∑ c ∈ s.erase b, ∏ a ∈ (s.erase b).erase c, (X - C (ζ ^ a)))
        = P * (1 / d b * (S1 - 1 / d b)) := by
      intro b hb
      rw [eval_finsetSum, hS1, ← sum_erase_eq_sub hb, mul_sum, mul_sum]
      refine sum_congr rfl fun c hc => ?_
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      rw [herase2 b hb c hc]
      have := hdnz b hb
      have := hdnz c (mem_of_mem_erase hc)
      field_simp
    rw [sum_congr rfl this, ← mul_sum, hS2]
    congr 1
    have hsplit : ∀ b ∈ s, 1 / d b * (S1 - 1 / d b) = S1 * (1 / d b) - 1 / d b ^ 2 := by
      intro b hb
      have := hdnz b hb
      field_simp
    rw [sum_congr rfl hsplit, sum_sub_distrib, ← mul_sum, ← hS1]

  have hterm : ∑ j ∈ s, ζ ^ j / (1 - ζ ^ j) ^ 2 = S2 - S1 := by
    rw [hS2, hS1, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    have := hdnz j hj
    simp only [hd] at this ⊢
    field_simp
    ring
  rw [hterm]
  rw [hA] at ha
  rw [hB] at hb
  rw [hP] at ha hb

  have hS1v : S1 = ((p : K) - 1) / 2 := by
    rw [eq_div_iff (two_ne_zero : (2 : K) ≠ 0)]
    apply mul_left_cancel₀ hpK
    linear_combination ha
  have hS2v : S2 = ((p : K) - 1) ^ 2 / 4 - ((p : K) - 1) * (p - 2) / 3 := by
    have h3 : (3 : K) ≠ 0 := by norm_num
    have : S1 * S1 - S2 = ((p : K) - 1) * (p - 2) / 3 := by
      rw [eq_div_iff h3]
      apply mul_left_cancel₀ hpK
      linear_combination hb
    rw [hS1v] at this
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    field_simp at this
    field_simp
    linear_combination -this
  rw [hS1v, hS2v]
  field_simp
  ring

private lemma sum_Icc_x [CharZero K] (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp : 3 ≤ p) :
    ∑ k ∈ Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2 = -((p : K) ^ 2 - 1) / 24 := by
  have h := sum_Ico_x hζ hp
  rw [sum_Ico_fold hodd (fun j => ζ ^ j / (1 - ζ ^ j) ^ 2)] at h
  have h2 : ∑ k ∈ Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2 + ζ ^ (p - k) / (1 - ζ ^ (p - k)) ^ 2)
      = 2 * ∑ k ∈ Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [x_reflect hζ (by have := (mem_Icc.mp hk).2; omega)]
    ring
  rw [h2] at h
  have h3 : ∑ k ∈ Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2
      = (2 * ∑ k ∈ Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2) / 2 := by
    field_simp
  rw [h3, h]
  ring

private lemma xdiff' {a b : K} (ha : (1 : K) - a ≠ 0) (hb : (1 : K) - b ≠ 0) :
    a / (1 - a) ^ 2 - b / (1 - b) ^ 2 = (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
  rw [div_sub_div _ _ (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)]
  congr 1
  ring

private lemma prod_sq_at_param (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) {w : K}
    (hw1 : (1 : K) - w ≠ 0) :
    ∏ k ∈ Icc 1 (p / 2), (w / (1 - w) ^ 2 - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
      = (∑ i ∈ range p, w ^ i) ^ 2 / ((p : K) ^ 2 * ((1 - w) ^ 2) ^ (p - 1)) := by
  have hp0 : 0 < p := hodd.pos
  have hfold : ∏ k ∈ Icc 1 (p / 2), (w / (1 - w) ^ 2 - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
      = ∏ j ∈ Ico 1 p, (w / (1 - w) ^ 2 - ζ ^ j / (1 - ζ ^ j) ^ 2) := by
    rw [prod_Ico_fold hodd]
    refine prod_congr rfl fun k hk => ?_
    rw [x_reflect hζ (by have := (mem_Icc.mp hk).2; omega), sq]
  rw [hfold]
  have hterm : ∀ j ∈ Ico 1 p, w / (1 - w) ^ 2 - ζ ^ j / (1 - ζ ^ j) ^ 2
      = (w - ζ ^ j) * (1 - w * ζ ^ j) / ((1 - w) ^ 2 * (1 - ζ ^ j) ^ 2) := fun j hj =>
    xdiff' hw1 (one_sub_pow_ne_zero hζ hj)
  rw [prod_congr rfl hterm, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_const,
    Nat.card_Ico, prod_pow, prod_Ico_sub hζ hp0, prod_Ico_one_sub hζ hp0,
    prod_Ico_one_sub_pow hζ hp0]
  ring

private lemma rhs_at_param (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) {w : K}
    (hw1 : (1 : K) - w ≠ 0) :
    (w / (1 - w) ^ 2) ^ p / ∏ k ∈ Icc 1 (p / 2), (w / (1 - w) ^ 2 - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
      = (p : K) ^ 2 * w ^ p / (1 - w ^ p) ^ 2 := by
  rw [prod_sq_at_param hζ hodd hw1, ← one_sub_mul_geom w p]
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hodd.pos; omega⟩
  have hD : ((1 : K) - w) ^ 2 ≠ 0 := pow_ne_zero 2 hw1
  have key : (w / (1 - w) ^ 2) ^ (m + 1) * (((m + 1 : ℕ) : K) ^ 2 * ((1 - w) ^ 2) ^ (m + 1 - 1))
      = ((m + 1 : ℕ) : K) ^ 2 * w ^ (m + 1) / (1 - w) ^ 2 := by
    rw [Nat.add_sub_cancel, div_pow, pow_succ ((1 - w) ^ 2) m, div_mul_eq_mul_div,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero m hD) hD) hD]
    ring
  rw [div_div_eq_mul_div, key, div_div, mul_pow]

private lemma lhs_at_param [CharZero K] (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp : 3 ≤ p)
    {w : K} (hwp : w ^ p ≠ 1) :
    w / (1 - w) ^ 2 + ∑ k ∈ Icc 1 (p / 2),
        (w * ζ ^ k / (1 - w * ζ ^ k) ^ 2 + w * ζ ^ (p - k) / (1 - w * ζ ^ (p - k)) ^ 2
          - 2 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
      - ((p : K) ^ 2 - 1) / 12
      = (p : K) ^ 2 * w ^ p / (1 - w ^ p) ^ 2 := by
  have hp0 : 0 < p := hodd.pos
  rw [sum_sub_distrib, ← mul_sum, sum_Icc_x hζ hodd hp,
    ← sum_Ico_fold hodd (fun j => w * ζ ^ j / (1 - w * ζ ^ j) ^ 2), ← orbit_sum_x hζ hwp,
    Finset.sum_range_eq_add_Ico _ hp0, pow_zero, mul_one]
  ring

end Aux13

section Assembly

private lemma param_identity {F : Type*} [Field F] [CharZero F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (X : F)
    (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2)
    {w : F} (hw1 : w ≠ 1) (hXw : X = w / (1 - w) ^ 2) :
    X + ∑ k ∈ Finset.Icc 1 (p / 2),
        (ζ ^ k / (1 - ζ ^ k) ^ 2 * (1 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2)) / (X - ζ ^ k / (1 - ζ ^ k) ^ 2)
          + (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 * (1 + 4 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
              / (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
      - ((p : F) ^ 2 - 1) / 12
      = X ^ p / ∏ k ∈ Finset.Icc 1 (p / 2), (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hwp : w ^ p ≠ 1 := pow_ne_one_of_good hp hζ hw1 hXw hX
  have hw1' : (1 : F) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  rw [Finset.sum_congr rfl (fun k hk => perk_at hp hζ hw1 hXw hX hk)]
  subst hXw
  rw [lhs_at_param hζ hodd hp3 hwp, rhs_at_param hζ hodd hw1']

private lemma exists_param {L : Type*} [Field L] [IsAlgClosed L] (Y : L) :
    ∃ w : L, w ≠ 1 ∧ Y = w / (1 - w) ^ 2 := by
  by_cases hY : Y = 0
  · exact ⟨0, zero_ne_one, by simp [hY]⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (C Y * X ^ 2 + C (-(2 * Y + 1)) * X + C Y)
      (by rw [degree_quadratic hY]; decide)
    have hw' : Y * w ^ 2 - (2 * Y + 1) * w + Y = 0 := by
      have := hw.eq_zero
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at this
      linear_combination this
    have hw1 : w ≠ 1 := by
      rintro rfl
      have h : (-1 : L) = 0 := by linear_combination hw'
      exact one_ne_zero (neg_eq_zero.mp h)
    refine ⟨w, hw1, ?_⟩
    rw [eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hw1)))]
    linear_combination hw'

end Assembly

theorem solution {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (X : F) (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2) :
    X + ∑ k ∈ Finset.Icc 1 (p / 2),
        (ζ ^ k / (1 - ζ ^ k) ^ 2 * (1 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2)) / (X - ζ ^ k / (1 - ζ ^ k) ^ 2)
          + (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 * (1 + 4 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
              / (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
      - ((p : F) ^ 2 - 1) / 12
      = X ^ p / ∏ k ∈ Finset.Icc 1 (p / 2), (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 := by
  let L := AlgebraicClosure F
  let ι : F →+* L := algebraMap F L
  have hι : Function.Injective ι := ι.injective
  have hζ' : IsPrimitiveRoot (ι ζ) p := hζ.map_of_injective hι
  have hX' : ∀ k ∈ Finset.Icc 1 (p / 2), ι X ≠ ι ζ ^ k / (1 - ι ζ ^ k) ^ 2 := by
    intro k hk h
    apply hX k hk
    apply hι
    rw [h]
    simp only [map_div₀, map_pow, map_sub, map_one]
  obtain ⟨w, hw1, hXw⟩ := exists_param (ι X)
  have key := param_identity hp hp2 hζ' (ι X) hX' hw1 hXw
  apply hι
  simp only [map_add, map_sub, map_mul, map_div₀, map_pow, map_sum, map_prod, map_natCast,
    map_one, map_ofNat]
  exact key

end S_cyclotomic_velu_xLaw
end P2MW
export P2MW.S_cyclotomic_velu_xLaw (solution)
