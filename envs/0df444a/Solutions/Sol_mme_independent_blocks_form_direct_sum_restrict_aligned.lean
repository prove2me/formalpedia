-- Prove2me | solution 1 for mme_independent_blocks_form_direct_sum_restrict_aligned
-- status  : ACCEPTED   (disprove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T13:40:01.722043+00:00
-- url     : https://prove2.me/submissions/01233772-d37c-4e24-a8e6-8ebf37042f81

import Mathlib.Tactic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000

private noncomputable abbrev source : TensorObj ℚ 3 :=
  { V := fun _ => ℚ, t := PiTensorProduct.tprod ℚ (fun _ => (1 : ℚ)) }

private noncomputable def grading : source.TypeGrading 2 where
  decomp _ a := if a = 0 then ⊤ else ⊥
  is_internal _ := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1)
      (by decide) (by ext a; fin_cases a <;> simp)]
    simpa using (isCompl_top_bot : IsCompl (⊤ : Submodule ℚ ℚ) ⊥)

private def zeroAddress : Fin 3 → Fin 2 := fun _ => 0
private def oneAddress : Fin 3 → Fin 2 := fun _ => 1
private def addresses : Finset (Fin 3 → Fin 2) := {zeroAddress, oneAddress}

private theorem addresses_card : addresses.card = 2 := by
  have h : zeroAddress ≠ oneAddress := by
    intro h; have hh := congrFun h 0; exact (by decide : (0 : Fin 2) ≠ 1) hh
  simp [addresses, h]

private noncomputable def unitVector (i : Fin 3) : grading.classOf i 0 := ⟨1, by trivial⟩
private noncomputable abbrev block : TensorObj ℚ 3 :=
  { V := fun i => grading.classOf i 0,
    fin := fun i => TensorObj.TypeGrading.classOf_finite grading i 0,
    t := grading.blockTensor zeroAddress }

private theorem project_zero (i : Fin 3) : grading.blockProj i 0 1 = unitVector i := by
  change (LinearEquiv.ofBijective (DirectSum.coeLinearMap (grading.decomp i))
    (grading.is_internal i)).symm (unitVector i).val 0 = unitVector i
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same _ _

private theorem block_tensor : block.t = PiTensorProduct.tprod ℚ unitVector := by
  simp only [block, TensorObj.TypeGrading.blockTensor, source, map_tprod]
  exact congrArg (PiTensorProduct.tprod ℚ) (funext project_zero)

private theorem grading_supported (σ : Fin 3 → Fin 2) (hσ : σ ∉ addresses) :
    grading.blockTensor σ = 0 := by
  have hn : σ ≠ zeroAddress := by intro h; subst h; simp [addresses] at hσ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ 0 := by
    exact not_forall.mp (fun h => hn (funext h))
  have hp : grading.blockProj i (σ i) 1 = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot ℚ).mp (by
      simpa [TensorObj.TypeGrading.classOf, grading, hi] using
        (grading.blockProj i (σ i) 1).property)
  simp only [TensorObj.TypeGrading.blockTensor, source, map_tprod]
  exact (PiTensorProduct.tprod ℚ).map_coord_zero i hp

private theorem addresses_disjoint :
    ∀ σ ∈ addresses, ∀ σ' ∈ addresses, σ ≠ σ' → ∀ i, σ i ≠ σ' i := by
  intro σ hσ σ' hσ' hn i
  simp only [addresses, Finset.mem_insert, Finset.mem_singleton] at hσ hσ'
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
  · exact (hn rfl).elim
  · change (0 : Fin 2) ≠ 1
    decide
  · change (1 : Fin 2) ≠ 0
    decide
  · exact (hn rfl).elim

private noncomputable def coord (i : Fin 3) (right : Bool) :
    ((grading.classOf i 0) × (grading.classOf i 0)) →ₗ[ℚ] ℚ :=
  (grading.classOf i 0).subtype.comp
    (if right then LinearMap.snd ℚ _ _ else LinearMap.fst ℚ _ _)

private noncomputable def evaluate (bits : Fin 3 → Bool) :
    PiTensorProduct ℚ (fun i : Fin 3 =>
      (grading.classOf i 0) × (grading.classOf i 0)) →ₗ[ℚ] ℚ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℚ (Fin 3) ℚ).compLinearMap
    (fun i => coord i (bits i)))

private theorem no_double : ¬ TensorObj.Restrict (TensorObj.add block block) source := by
  rintro ⟨f, hf⟩
  let v (i : Fin 3) : (grading.classOf i 0) × (grading.classOf i 0) := f i 1
  have hh : PiTensorProduct.tprod ℚ v =
      PiTensorProduct.tprod ℚ (fun i => (unitVector i, 0)) +
      PiTensorProduct.tprod ℚ (fun i => (0, unitVector i)) := by
    change PiTensorProduct.map f (PiTensorProduct.tprod ℚ (fun _ : Fin 3 => (1 : ℚ))) =
      PiTensorProduct.map (fun i => LinearMap.inl ℚ (block.V i) (block.V i)) block.t +
      PiTensorProduct.map (fun i => LinearMap.inr ℚ (block.V i) (block.V i)) block.t at hf
    rw [block_tensor, map_tprod, map_tprod, map_tprod] at hf
    exact hf
  have h0 := congrArg (evaluate ![false, false, false]) hh
  have h1 := congrArg (evaluate ![true, true, true]) hh
  have hm := congrArg (evaluate ![false, false, true]) hh
  simp [evaluate, coord, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three, unitVector] at h0 h1 hm
  have hn0 : (v 0).1.val * (v 1).1.val ≠ 0 := by
    intro hz; rw [hz, zero_mul] at h0; norm_num at h0
  have hn1 : (v 2).2.val ≠ 0 := by
    intro hz; rw [hz, mul_zero] at h1; norm_num at h1
  rcases hm with (ha | hb) | hc
  · apply hn0
    simp [ha]
  · apply hn0
    simp [hb]
  · apply hn1
    simp [hc]

theorem solution : ¬ ∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (C : Finset (Fin 3 → Fin t))
    (_hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin 3, σ i ≠ σ' i)
    (_hSupp : ∀ σ : Fin 3 → Fin t, σ ∉ C → G.blockTensor σ = 0)
    (B : Fin C.card → TensorObj K 3)
    (_hB : ∀ j : Fin C.card, ∃ σ ∈ C, B j = G.blockSubtensor σ),
    TensorObj.Restrict (TensorObj.bigAdd B) T := by
  intro h
  have hr := h grading addresses addresses_disjoint grading_supported (fun _ => block)
    (fun _ => ⟨zeroAddress, by simp [addresses], rfl⟩)
  have heq : TensorObj.bigAdd (fun _ : Fin addresses.card => block) =
      TensorObj.add block block := by
    rw [addresses_card]
    rfl
  rw [heq] at hr
  exact no_double hr
