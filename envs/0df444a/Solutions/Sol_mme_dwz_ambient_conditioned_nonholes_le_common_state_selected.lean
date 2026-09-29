-- Prove2me | solution 1 for mme_dwz_ambient_conditioned_nonholes_le_common_state_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T02:56:38.253172+00:00
-- url     : https://prove2.me/submissions/8a5b821f-1511-4e1c-b853-c9699e14edc0

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy
import Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
import Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
import Theorems.Thm_mme_dwz_affine_common_state_XZ_iff_conditioned

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-!
# Ambient conditioned mass survives selected-family restriction

The Claim-6.8 mass is first counted against every exact-profile competitor
with the owner's coarse Z word.  The final source family contains only the
enumerated selected owners.  This theorem is the exact termwise monotonicity
bridge between those two broken copies.
-/

theorem solution
    (m : ℕ) {p N L k : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset (ZMod p))
    (T : Finset (Fin L → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin k → Fin (N + 1) → Fin 15)
    (hedgeT : ∀ j, MME.DWZGlobalCorrelated.sourceWord reindex edge j ∈ T)
    (hedgeInjective : Function.Injective edge)
    (r : Fin k)
    (hretains : MME.dwzAsymmetricAffineRetains (4 : ZMod p) S
      (MME.dwzTable2CastX (edge r))
      (MME.dwzTable2CastY (edge r))
      (MME.dwzTable2CastZ (edge r)) q) :
    let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
    let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained t)
    let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
    let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Fin L → Fin (3 * 3) := fun z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Outer → Prop := fun z A ↦
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let addressX : Outer → Fin (N + 1) → Fin 5 := fun A t ↦
      MME.DWZSquare.shapeX (A.1 (reindex t))
    let addressZ : Fin (N + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
    let conditionedW0 : ZMod p :=
      2 * (∑ t,
        (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
          ZMod p) * weight t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t
    let hashRetained : Outer → Prop := fun A ↦
      (∑ t, (((addressX A) t).val : ZMod p) * weight t) =
        (2 : ZMod p)⁻¹ *
          (conditionedW0 +
            ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t)
    let retainedOuter : Outer := by
      refine ⟨retained, hedgeT r, ?_⟩
      intro t
      rfl
    let ambientCopy : MME.DWZSquare.BrokenBlockCopy
        (MME.DWZTable2StandardForm.UsefulBlock m retained) := by
      classical
      exact MME.DWZStep2.brokenCopy
        (fun z A ↦ compatible z A ∧ hashRetained A)
        (fun _ _ ↦ True) retainedOuter
    ambientCopy.nonholes.card ≤
      (MME.DWZGlobalCorrelated.commonStateBrokenCopy
        m reindex q edge r).nonholes.card := by
  classical
  dsimp only
  let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
  let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ t, MME.DWZSquare.shapeZ (w t) =
      MME.DWZSquare.shapeZ (retained t)
  let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
  let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Fin L → Fin (3 * 3) := fun z t ↦
    MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
  let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
      Outer → Prop := fun z A ↦
    MME.DWZStep2Source.retainedFineCompatible m
      (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
  let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
  let addressX : Outer → Fin (N + 1) → Fin 5 := fun A t ↦
    MME.DWZSquare.shapeX (A.1 (reindex t))
  let addressZ : Fin (N + 1) → Fin 5 := fun t ↦
    MME.DWZSquare.shapeZ (retained (reindex t))
  let conditionedW0 : ZMod p :=
    2 * (∑ t,
      (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
        ZMod p) * weight t) -
      ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t
  let hashRetained : Outer → Prop := fun A ↦
    (∑ t, (((addressX A) t).val : ZMod p) * weight t) =
      (2 : ZMod p)⁻¹ *
        (conditionedW0 +
          ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t)
  let retainedOuter : Outer := ⟨retained, hedgeT r, fun _ ↦ rfl⟩
  let P : Fin k → Prop := fun j ↦
    MME.DWZGlobalCorrelated.sameCoarseZ edge r j
  let Small := Subtype P
  let f : Small → Outer := fun j ↦ ⟨
    MME.DWZGlobalCorrelated.sourceWord reindex edge j.1,
    hedgeT j.1,
    by
      intro t
      have ht := j.2 (reindex.symm t)
      exact ht⟩
  have hf : Function.Injective f := by
    intro j j' hjj'
    apply Subtype.ext
    apply hedgeInjective
    funext t
    have ht := congrFun (congrArg Subtype.val hjj') (reindex t)
    simpa only [f, MME.DWZGlobalCorrelated.sourceWord,
      Equiv.symm_apply_apply] using ht
  have hsupport : ∀ t,
      MME.dwzTable2CastX (p := p) (edge r) t +
          MME.dwzTable2CastY (edge r) t +
          MME.dwzTable2CastZ (edge r) t = (4 : ZMod p) := by
    intro t
    have hs := MME.DWZSquare.shape_sum (edge r t)
    have hc := congrArg (fun x : ℕ ↦ (x : ZMod p)) hs
    simpa only [MME.dwzTable2CastX, MME.dwzTable2CastY,
      MME.dwzTable2CastZ, Nat.cast_add, Nat.cast_ofNat] using hc
  have hcompat : ∀ z j,
      MME.DWZGlobalCorrelated.ownerCompatible
          m reindex q edge r z j.1 ↔
        compatible z (f j) ∧ hashRetained (f j) := by
    intro z j
    have hhash := mme_dwz_affine_common_state_XZ_iff_conditioned
      hpodd S (MME.dwzTable2CastX (edge r))
        (MME.dwzTable2CastY (edge r))
        (MME.dwzTable2CastZ (edge r))
        (MME.dwzTable2CastX (edge j.1)) hsupport q hretains
    constructor
    · rintro ⟨_hZ, hFine, hHash⟩
      refine ⟨?_, ?_⟩
      · exact hFine
      · have hCommon :
            MME.dwzAsymmetricHashX
                (MME.dwzAsymmetricHashStateOfAffine q)
                (MME.dwzTable2CastX (edge j.1)) =
              MME.dwzAsymmetricHashZ (4 : ZMod p)
                (MME.dwzAsymmetricHashStateOfAffine q)
                (MME.dwzTable2CastZ (edge r)) := by
          simpa only [MME.DWZGlobalCorrelated.commonStateHashRetained] using
            hHash
        have hConditioned := hhash.mp hCommon
        simpa only [hashRetained, f, retained, weight, addressX, addressZ,
          conditionedW0, MME.DWZGlobalCorrelated.sourceWord,
          MME.dwzTable2CastX, MME.dwzTable2CastZ,
          Equiv.symm_apply_apply] using hConditioned
    · rintro ⟨hFine, hHash⟩
      refine ⟨j.2, ?_, ?_⟩
      · exact hFine
      · have hConditioned :
            (∑ t,
                MME.dwzTable2CastX (p := p) (edge j.1) t *
                  q.1 t.castSucc) =
              (2 : ZMod p)⁻¹ *
                (2 * (∑ t,
                    MME.dwzTable2CastX (p := p) (edge r) t *
                      q.1 t.castSucc) -
                    ∑ t, ((4 : ZMod p) -
                      MME.dwzTable2CastZ (p := p) (edge r) t) *
                        q.1 t.castSucc +
                  ∑ t, ((4 : ZMod p) -
                    MME.dwzTable2CastZ (p := p) (edge r) t) *
                      q.1 t.castSucc) := by
          simpa only [hashRetained, f, retained, weight, addressX, addressZ,
            conditionedW0, MME.DWZGlobalCorrelated.sourceWord,
            MME.dwzTable2CastX, MME.dwzTable2CastZ,
            Equiv.symm_apply_apply] using hHash
        have hCommon := hhash.mpr hConditioned
        simpa only [MME.DWZGlobalCorrelated.commonStateHashRetained,
          MME.dwzTable2CastX, MME.dwzTable2CastZ] using hCommon
  have hmono := mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
    (fun z (j : Small) ↦
      MME.DWZGlobalCorrelated.ownerCompatible m reindex q edge r z j.1)
    (fun _ (_ : Small) ↦ True)
    (fun z A ↦ compatible z A ∧ hashRetained A)
    (fun _ (_ : Outer) ↦ True)
    f hf ⟨r, fun _ ↦ rfl⟩ hcompat (fun _ _ ↦ trivial)
  have hexact :=
    mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
      P
      (MME.DWZGlobalCorrelated.ownerCompatible m reindex q edge r)
      (fun _ (_ : Fin k) ↦ True) r (fun _ ↦ rfl)
      (fun _ j hj ↦ hj.1)
  exact hmono.trans_eq hexact.symm
