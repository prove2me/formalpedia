-- Prove2me | solution 1 for mme_dwz_lemma3_11_fixed_z_collision_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:00:51.473743+00:00
-- url     : https://prove2.me/submissions/52d17d03-0cb6-4fae-b04a-7e669f07fbdb

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false

/-!
An exact finite form of the conditional collision calculation in
Duan--Wu--Zhou, Lemma 3.11.  The random variable `w0` is solved from the
conditioning event for `I`; the remaining weights are still uniform, and a
distinct address `I'` imposes one nonzero linear equation on them.
-/

theorem solution
    {p n : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum b0 : ZMod p)
    (I I' K : Fin (n + 1) → ZMod p) (hII' : I ≠ I') :
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w A => b0 + ∑ t, A t * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w0 w C =>
        b0 + (2 : ZMod p)⁻¹ *
          (w0 + ∑ t, (levelSum - C t) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
      fun w =>
        2 * (∑ t, I t * w t) -
          ∑ t, (levelSum - K t) * w t
    (∀ w w0, hX w I = hZ w0 w K ↔ w0 = conditionedW0 w) ∧
      p * ((Finset.univ.filter
        (fun w : Fin (n + 1) → ZMod p =>
          hX w I' = hZ (conditionedW0 w) w K)).card) =
        Fintype.card (Fin (n + 1) → ZMod p) := by
  dsimp only
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  have htwo' : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [mul_comm, htwo]
  have hbase (w : Fin (n + 1) → ZMod p) :
      b0 + ∑ t, I t * w t =
        b0 + (2 : ZMod p)⁻¹ *
          ((2 * (∑ t, I t * w t) -
              ∑ t, (levelSum - K t) * w t) +
            ∑ t, (levelSum - K t) * w t) := by
    rw [sub_add_cancel]
    calc
      b0 + ∑ t, I t * w t =
          b0 + 1 * (∑ t, I t * w t) := by ring
      _ = b0 + ((2 : ZMod p)⁻¹ * 2) *
          (∑ t, I t * w t) := by rw [htwo]
      _ = b0 + (2 : ZMod p)⁻¹ *
          (2 * (∑ t, I t * w t)) := by ring
  constructor
  · intro w w0
    let S : ZMod p := ∑ t, I t * w t
    let T : ZMod p := ∑ t, (levelSum - K t) * w t
    constructor
    · intro h
      have h' : S = (2 : ZMod p)⁻¹ * (w0 + T) := by
        exact add_left_cancel h
      have hdouble : 2 * S = w0 + T := by
        calc
          2 * S = 2 * ((2 : ZMod p)⁻¹ * (w0 + T)) := by rw [h']
          _ = (2 * (2 : ZMod p)⁻¹) * (w0 + T) := by ring
          _ = w0 + T := by rw [htwo', one_mul]
      exact (eq_sub_iff_add_eq.mpr hdouble.symm)
    · intro hw0
      subst w0
      exact hbase w
  · let c : Fin (n + 1) → ZMod p := fun t => I' t - I t
    have hcne : c ≠ 0 := by
      intro hc
      apply hII'
      funext t
      have hct := congrFun hc t
      simp only [c, Pi.zero_apply] at hct
      exact (sub_eq_zero.mp hct).symm
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
    have hcj : c j ≠ 0 := by
      simpa using hj
    have hlinear :=
      mme_ZMod_prime_linear_hash_fiber_card c j hcj 0
    have hfilters :
        Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod p =>
              b0 + ∑ t, I' t * w t =
                b0 + (2 : ZMod p)⁻¹ *
                  ((2 * (∑ t, I t * w t) -
                      ∑ t, (levelSum - K t) * w t) +
                    ∑ t, (levelSum - K t) * w t)) =
          Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod p =>
              ∑ t, c t * w t = 0) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hbase w]
      rw [add_left_cancel_iff]
      change (∑ t, I' t * w t) = ∑ t, I t * w t ↔
        ∑ t, (I' t - I t) * w t = 0
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, sub_eq_zero]
    rw [hfilters, hlinear]
    simp [ZMod.card, pow_succ, Nat.mul_comm]
