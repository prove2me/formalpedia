-- Prove2me | solution 1 for syracuse_injective_orbit_yields_barrier_ancestors
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:13:50.106124+00:00
-- url     : https://prove2.me/submissions/188f8577-2e39-4b74-b65c-d787a05167c7

import Mathlib
import Theorems.Thm_syracuse_injective_last_exit_and_tail_minimum

open Nat

private theorem predecessor_at (a e : ℕ) (ha : 1 < a) (ho : a%2 = 1)
    (he : 2 ≤ e) (he' : e ≤ 7)
    (hmod : (2^e*a)%3 = 1) (hmod' : (2^e*a)%9 ≠ 1) :
    let b := (2^e*a-1)/3
    a < b ∧ b ≤ 43*a ∧ b%2 = 1 ∧ ¬ 3∣b ∧ syracuseStep b = a := by
  dsimp only
  let b := (2^e*a-1)/3
  have hlo := Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by decide : 0 < 2) he)
  have hhi := Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by decide : 0 < 2) he')
  norm_num at hlo hhi
  have hdiv : 3*b+1 = 2^e*a := by dsimp [b]; omega
  have hEven : 2 ∣ 2^e*a := (dvd_pow_self _ (by omega : e ≠ 0)).trans (dvd_mul_right _ _)
  have hg : syracuseStep b = a := by
    rw [syracuseStep, hdiv]
    exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two (by omega)
  have hb : b%2 = 1 := by omega
  have hb3 : ¬ 3 ∣ b := by omega
  exact ⟨by omega, by omega, hb, hb3, hg⟩

private theorem two_predecessors (a : ℕ) (ha : 1 < a) (ho : a%2 = 1) (h3 : ¬ 3 ∣ a) :
    ∃ b c : ℕ, b < c ∧
      (a < b ∧ b ≤ 43*a ∧ b%2 = 1 ∧ ¬ 3∣b ∧ syracuseStep b = a) ∧
      (a < c ∧ c ≤ 43*a ∧ c%2 = 1 ∧ ¬ 3∣c ∧ syracuseStep c = a) := by
  obtain ⟨e,f,he,hef,hf,hem,hen,hfm,hfn⟩ :
      ∃ e f : ℕ, 2 ≤ e ∧ e < f ∧ f ≤ 7 ∧ (2^e*a)%3 = 1 ∧ (2^e*a)%9 ≠ 1 ∧
        (2^f*a)%3 = 1 ∧ (2^f*a)%9 ≠ 1 := by
    have hcases : a%9=1 ∨ a%9=2 ∨ a%9=4 ∨ a%9=5 ∨ a%9=7 ∨ a%9=8 := by omega
    rcases hcases with h|h|h|h|h|h
    · refine ⟨2,4,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,7,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨2,6,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨3,5,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨4,6,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
    · refine ⟨5,7,by decide,by decide,by decide,?_,?_,?_,?_⟩ <;> norm_num <;> omega
  let b := (2^e*a-1)/3
  let c := (2^f*a-1)/3
  have hb := predecessor_at a e ha ho he (by omega) hem hen
  have hc := predecessor_at a f ha ho (by omega) hf hfm hfn
  have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hef
  have hprod := Nat.mul_lt_mul_of_pos_right hpow (by omega : 0 < a)
  have hbexact : 3*b+1 = 2^e*a := by dsimp [b]; omega
  have hcexact : 3*c+1 = 2^f*a := by dsimp [c]; omega
  refine ⟨b,c,?_,hb,hc⟩
  omega

private theorem large_coprime_ancestors (a d : ℕ)
    (ha : 1 < a) (ho : a%2 = 1) (h3 : ¬ 3 ∣ a) :
    ∃ S : Finset ℕ, S.card = 2^d ∧ ∀ b ∈ S,
      b ≤ 43^d*a ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
      syracuseStep^[d] b = a ∧ ∀ i ≤ d, a ≤ syracuseStep^[i] b := by
  classical
  induction d with
  | zero =>
    refine ⟨{a}, by simp, ?_⟩
    intro b hb
    have heq : b = a := Finset.mem_singleton.mp hb
    subst b
    simp [ho, h3]
  | succ d ih =>
    obtain ⟨S,hcard,hS⟩ := ih
    have hChildren (p : {p // p ∈ S}) := by
      obtain ⟨_,hodd, hnot3,_,hfloor⟩ := hS p p.property
      have hp : a ≤ p := by simpa using hfloor 0 (Nat.zero_le _)
      exact two_predecessors p (ha.trans_le hp) hodd hnot3
    choose l u hlt hl hu using hChildren
    let f (w : Bool × {p // p ∈ S}) := if w.1 then u w.2 else l w.2
    have hp (w : Bool × {p // p ∈ S}) :
        (w.2 : ℕ) < f w ∧ f w ≤ 43*w.2 ∧
          f w%2 = 1 ∧ ¬ 3∣f w ∧ syracuseStep (f w) = w.2 := by
      rcases w with ⟨b,p⟩
      cases b
      · simpa [f] using hl p
      · simpa [f] using hu p
    have hf : Function.Injective f := by
      rintro ⟨b,p⟩ ⟨c,q⟩ h
      have heq : p = q := by
        apply Subtype.ext
        exact (hp (b,p)).2.2.2.2.symm.trans ((congrArg syracuseStep h).trans (hp (c,q)).2.2.2.2)
      subst q
      cases b <;> cases c <;> try rfl
      · exact False.elim ((Nat.ne_of_lt (hlt p)) (by simpa [f] using h))
      · exact False.elim ((Nat.ne_of_lt (hlt p)) (by simpa [f] using h.symm))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, Fintype.card_coe, hcard, pow_succ, Nat.mul_comm]
    · intro b hb
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hb,hle,hOdd,hThree,heq⟩ := hp w
      obtain ⟨hP,_,_,hvisit,hfloor⟩ := hS w.2 w.2.property
      refine ⟨?_,hOdd,hThree,?_,?_⟩
      · calc
          f w ≤ 43 * (w.2 : ℕ) := hle
          _ ≤ 43 * (43^d*a) := Nat.mul_le_mul_left _ hP
          _ = 43^(d+1)*a := by rw [_root_.pow_succ']; ac_rfl
      · rwa [Function.iterate_succ_apply,heq]
      · intro i hi
        cases i with
        | zero =>
          have hP0 : a ≤ (w.2 : ℕ) := by simpa using hfloor 0 (Nat.zero_le _)
          exact hP0.trans hb.le
        | succ i =>
          rw [Function.iterate_succ_apply,heq]
          exact hfloor i (by omega)


theorem solution (n B d : ℕ)
    (hodd : n % 2 = 1) (hB : 1 < B) (hnB : n < B)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    ∃ j : ℕ, ∃ S : Finset ℕ, S.card = 2^d ∧
      ∀ b ∈ S, 2*b ≤ 3*43^d*B ∧ b%2 = 1 ∧ ¬ 3 ∣ b ∧
        syracuseStep^[d] b = syracuseStep^[j] n ∧
        (∀ i : ℕ, B ≤ syracuseStep^[i] b) ∧
        Function.Injective (fun i : ℕ => syracuseStep^[i] b) := by
  obtain ⟨k,j,hkj,_,_,_,hBmin,hUpper,hMod,hmin⟩ :=
    syracuse_injective_last_exit_and_tail_minimum n B hodd hB hnB hinj
  let a := syracuseStep^[j] n
  have ha : 1 < a := hB.trans_le hBmin
  change a%12 = 7 ∨ a%12 = 11 at hMod
  have hoddA : a%2 = 1 := by omega
  have hthreeA : ¬ 3 ∣ a := by omega
  obtain ⟨S,hCard,hS⟩ := large_coprime_ancestors a d ha hoddA hthreeA
  refine ⟨j,S,hCard,?_⟩
  intro b hb
  obtain ⟨hSize,hOdd,hThree,hRoot,hFloor⟩ := hS b hb
  have hAt (i : ℕ) : syracuseStep^[i+d] b = syracuseStep^[i+j] n := by
    rw [Function.iterate_add_apply, hRoot, Function.iterate_add_apply]
  refine ⟨?_,hOdd,hThree,hRoot,?_,?_⟩
  · change 2*a+2 ≤ 3*B at hUpper
    calc
      2*b ≤ 2*(43^d*a) := Nat.mul_le_mul_left _ hSize
      _ = 43^d*(2*a) := by ac_rfl
      _ ≤ 43^d*(3*B) := Nat.mul_le_mul_left _ (by omega)
      _ = 3*43^d*B := by ac_rfl
  · intro i
    by_cases hi : i ≤ d
    · exact hBmin.trans (hFloor i hi)
    · obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le (show d ≤ i by omega)
      rw [Nat.add_comm d e, hAt]
      exact hBmin.trans (hmin (e+j) (by omega))
  · intro i l hEq
    have hShift := congrArg (syracuseStep^[d]) hEq
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        Nat.add_comm d i, Nat.add_comm d l, hAt, hAt] at hShift
    exact Nat.add_right_cancel (hinj hShift)
