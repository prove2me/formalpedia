-- Prove2me | solution 1 for mme_Ctensor_three_balanced_cyclic_induced_matching_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:46:48.43784+00:00
-- url     : https://prove2.me/submissions/801b7766-464c-437b-b740-0cc6b30f19fc

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_Ctensor_three_cyclic_balanced_grading_certificate
import Theorems.Thm_mme_Ctensor_balanced_word_card
import Theorems.Thm_mme_Ctensor_balanced_weight_sqrt_loss
import Theorems.Thm_mme_MM_support_behrend_induced_matching
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators Filter

universe u

private theorem three_family_realization
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∀ (E : Finset (Fin W × Fin W × Fin W)),
      Function.Injective
          (fun e : E ↦ (e.1.1, e.1.2.1)) →
      Function.Injective
          (fun e : E ↦ (e.1.2.1, e.1.2.2)) →
      Function.Injective
          (fun e : E ↦ (e.1.2.2, e.1.1)) →
      (∀ x y z : E,
        x.1.2.1 = y.1.2.1 →
        y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 →
        x = y ∧ y = z) →
      ∃ (a b c : Fin E.card → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          ((threeStarCyclicProduct X Y Z).kronPow R) ∧
        (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  classical
  dsimp only
  let B :=
    {w : Fin (H * m) → Fin H // ∀ h,
      Fintype.card {j // w j = h} = m}
  let W : ℕ := Nat.card B
  let words : Fin W ≃ B := by
    dsimp [W]
    simpa only [Nat.card_eq_fintype_card] using (Fintype.equivFin B).symm
  obtain ⟨C⟩ :=
    mme_Ctensor_three_cyclic_balanced_grading_certificate
      certX certY certZ hH m W words
  intro E hx hy hz hinduced
  let enum : Fin E.card ≃ E := E.equivFin.symm
  let edge : Fin E.card → (Fin W × Fin W × Fin W) :=
    fun j ↦ (enum j).1
  let A : Fin E.card → Fin 3 → Fin (H * m) → Fin C.t :=
    fun j ↦ C.address (edge j)
  have hInduced : ∀ js : Fin 3 → Fin E.card,
      (∀ r : Fin (H * m),
        C.grading.blockTensor (fun i ↦ A (js i) i r) ≠ 0) →
      ∃ j : Fin E.card, js = fun _ ↦ j := by
    intro js hnonzero
    let es : Fin 3 → (Fin W × Fin W × Fin W) :=
      fun i ↦ edge (js i)
    have hs := C.mixed_support es (by
      intro r
      simpa only [es, A] using hnonzero r)
    have hmixed := hinduced (enum (js 1)) (enum (js 2)) (enum (js 0))
      hs.1 hs.2.1 hs.2.2
    have h12 : js 1 = js 2 := enum.injective hmixed.1
    have h20 : js 2 = js 0 := enum.injective hmixed.2
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact h12.trans h20
    · exact h20
  have hblocks : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        gradedAddressBlock C.grading (A j)))
      ((threeStarCyclicProduct X Y Z).kronPow (H * m)) :=
    mme_induced_graded_address_blocks_restrict C.grading A hInduced
  let a : Fin E.card → ℕ := fun j ↦ C.a (edge j)
  let b : Fin E.card → ℕ := fun j ↦ C.b (edge j)
  let c : Fin E.card → ℕ := fun j ↦ C.c (edge j)
  have hmm : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun j ↦
        gradedAddressBlock C.grading (A j))) := by
    apply mme_bigAdd_mono_restrict
    intro j
    exact (C.component (edge j)).1
  refine ⟨a, b, c, TensorObj.Restrict.trans hmm hblocks, ?_⟩
  intro j
  exact C.common_volume (edge j)

private theorem three_matching_extraction
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt
              (Real.log (((W + 1 : ℕ) : ℝ))))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  classical
  dsimp only
  let R : ℕ := H * m
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  have hprod : (∏ _h : Fin H, m.factorial) = m.factorial ^ H := by
    simp
  have hsum : (∑ _h : Fin H, m) = H * m := by
    simp
  have hdiv : (∏ _h : Fin H, m.factorial) ∣ (H * m).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin H)) (fun _ : Fin H ↦ m)
    rw [hsum] at h
    exact h
  have hid : W * m.factorial ^ H = R.factorial := by
    dsimp [W, R]
    rw [mme_Ctensor_balanced_word_card, ← hprod,
      Nat.div_mul_cancel hdiv]
  have hW : 0 < W := by
    by_contra hnot
    have hzero : W = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, zero_mul] at hid
    exact (Nat.factorial_pos R).ne' hid.symm
  obtain ⟨E, hx, hy, hz, hinduced, hcard⟩ :=
    mme_MM_support_behrend_induced_matching W hW
  obtain ⟨a, b, c, hrestrict, hvolume⟩ :=
    three_family_realization
      certX certY certZ hH m E hx hy hz hinduced
  refine ⟨E.card, a, b, c, ?_, ?_, ?_⟩
  · simpa [R] using hrestrict
  · simpa [W] using hcard
  · simpa [R] using hvolume

theorem solution
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt
              (Real.log (((W + 1 : ℕ) : ℝ))))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  exact three_matching_extraction certX certY certZ hH m
