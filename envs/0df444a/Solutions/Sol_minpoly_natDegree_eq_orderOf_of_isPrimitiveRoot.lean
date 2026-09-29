-- Prove2me | solution 1 for minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5bcc0958-3ae1-5a79-8a6d-f4dd42785721

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Polynomial

theorem solution
    (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (m : ℕ) (ζ : E) (hζ : IsPrimitiveRoot ζ m)
    (hm : (Fintype.card F).Coprime m) :
    (minpoly F ζ).natDegree = orderOf (ZMod.unitOfCoprime (Fintype.card F) hm) ∧
    ∀ x : E, Polynomial.aeval x (minpoly F ζ) = 0 ↔ ∃ i : ℕ, x = ζ ^ (Fintype.card F ^ i) := by
  classical

  set Q := Fintype.card F with hQdef
  have hQ : 1 < Q := Fintype.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hm
    omega
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  let u := ZMod.unitOfCoprime Q hm
  set e := orderOf u with hedef

  have hfrob : ∀ (k : ℕ) (g : F[X]) (x : E), Polynomial.aeval (x ^ (Q ^ k)) g = (Polynomial.aeval x g) ^ (Q ^ k) := by
    intro k g x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, pow_mul, ← ih]
      rw [← Polynomial.expand_aeval Q g, FiniteField.expand_card, map_pow]

  have hpow : ∀ k : ℕ, ζ ^ (Q ^ k) = ζ ↔ e ∣ k := by
    intro k
    have h1 : ζ ^ (Q ^ k) = ζ ↔ ζ ^ (Q ^ k - 1) = 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_pow k Q (by omega)), pow_succ]
      constructor
      · intro h
        have := mul_right_cancel₀ hζ0 (h.trans (one_mul ζ).symm)
        exact this
      · intro h; rw [h, one_mul]
    rw [h1, hζ.pow_eq_one_iff_dvd, ← Nat.modEq_iff_dvd' (Nat.one_le_pow k Q (by omega)), hedef,
      orderOf_dvd_iff_pow_eq_one]
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Nat.cast_pow, ← Units.val_inj, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Units.val_one]
    exact comm

  have hint : IsIntegral F ζ := by
    refine ⟨X ^ m - 1, monic_X_pow_sub_C 1 hm0, ?_⟩
    simp [hζ.pow_eq_one]
  let K := IntermediateField.adjoin F ({ζ} : Set E)
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  have hdK : Module.finrank F K = (minpoly F ζ).natDegree := IntermediateField.adjoin.finrank hint
  haveI : Finite K := Module.finite_of_finite F
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Q ^ (minpoly F ζ).natDegree := by
    rw [← hdK]; exact Module.card_eq_pow_finrank
  set d := (minpoly F ζ).natDegree with hddef

  have hed : e ∣ d := by
    rw [← hpow]
    have hζK : ζ ∈ K := IntermediateField.mem_adjoin_simple_self F ζ
    have := FiniteField.pow_card (⟨ζ, hζK⟩ : K)
    rw [hcardK] at this
    exact congrArg Subtype.val this

  have hepos : 0 < e := orderOf_pos u
  have hζe : ζ ^ (Q ^ e) = ζ := (hpow e).2 dvd_rfl
  have hrootK : ∀ y : K, (y : E) ^ (Q ^ e) = y := by
    intro y
    have hy : (y : E) ∈ (IntermediateField.adjoin F ({ζ} : Set E)).toSubalgebra := y.2
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨g, hg⟩ := hy
    rw [← hg]
    show (Polynomial.aeval ζ g) ^ (Q ^ e) = Polynomial.aeval ζ g
    rw [← hfrob, hζe]
  have hde : d ≤ e := by

    let P : E[X] := X ^ (Q ^ e) - X
    have hQe : 1 < Q ^ e := Nat.one_lt_pow hepos.ne' hQ
    have hPdeg : P.natDegree = Q ^ e := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hQe]
    have hP0 : P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hPdeg
      have := Nat.one_le_pow e Q (by omega)
      omega
    have hsub : Finset.univ.image (fun y : K => (y : E)) ⊆ P.roots.toFinset := by
      intro z hz
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, hrootK, sub_self]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcardK] at hcard
    have : P.roots.toFinset.card ≤ Q ^ e :=
      (Multiset.toFinset_card_le _).trans (hPdeg ▸ Polynomial.card_roots' P)
    exact (Nat.pow_le_pow_iff_right hQ).1 (hcard.trans this)
  have hdeq : d = e := le_antisymm hde (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    rw [hddef]; exact (minpoly.natDegree_pos hint).ne')) hed)
  refine ⟨hdeq, fun x => ?_⟩

  have hroot_pow : ∀ i : ℕ, Polynomial.aeval (ζ ^ (Q ^ i)) (minpoly F ζ) = 0 := by
    intro i; rw [hfrob, minpoly.aeval, zero_pow (Nat.pos_of_ne_zero (by positivity)).ne']
  constructor
  · intro hx

    have hinj : Function.Injective (fun i : Fin e => ζ ^ (Q ^ (i : ℕ))) := by
      intro i j hij
      simp only at hij
      wlog hle : (i : ℕ) ≤ j generalizing i j
      · exact (this hij.symm (le_of_lt (not_le.1 hle))).symm

      have h1 : ζ ^ (Q ^ ((i : ℕ) + (e - j))) = ζ := by
        rw [pow_add, pow_mul, hij, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_of_lt j.2), hζe]
      have h2 : e ∣ (i : ℕ) + (e - j) := (hpow _).1 h1
      apply Fin.ext
      obtain ⟨c, hc⟩ := h2
      have hj := j.2
      have : c = 1 := by
        rcases c with _ | _ | c
        · omega
        · rfl
        · exfalso
          have h3 : e * (c + 1 + 1) = e * c + e + e := by ring
          omega
      subst this
      omega
    let R : Finset E := Finset.univ.image (fun i : Fin e => ζ ^ (Q ^ (i : ℕ)))
    have hRcard : R.card = e := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    let Pm : E[X] := (minpoly F ζ).map (algebraMap F E)
    have hPm0 : Pm ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hmemPm : ∀ z : E, z ∈ Pm.roots.toFinset ↔ Polynomial.aeval z (minpoly F ζ) = 0 := by
      intro z
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPm0, Polynomial.IsRoot, Polynomial.eval_map,
        ← Polynomial.aeval_def]
    have hRsub : R ⊆ Pm.roots.toFinset := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (hmemPm _).2 (hroot_pow i)
    have hcard : Pm.roots.toFinset.card ≤ R.card := by
      rw [hRcard, ← hdeq]
      refine (Multiset.toFinset_card_le _).trans ?_
      have := Polynomial.card_roots' Pm
      rwa [Polynomial.natDegree_map] at this
    have hReq : R = Pm.roots.toFinset := Finset.eq_of_subset_of_card_le hRsub hcard
    have hxR : x ∈ R := by rw [hReq]; exact (hmemPm x).2 hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hxR
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact hroot_pow i

end S_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
end P2MW
export P2MW.S_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot (solution)
