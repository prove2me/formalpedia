-- Prove2me | solution 1 for mme_dwz_global_exact_profile_competitor_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:49:17.162982+00:00
-- url     : https://prove2.me/submissions/a680c576-8266-4dcc-89d0-ae8b6b01ac43

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_count_upper
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Mathlib.Data.Finite.Card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (T : Finset (Position → Fin 15))
    (hTExact : ∀ w ∈ T, ∀ s,
      Fintype.card {t : Position // w t = s} =
        MME.DWZTable2Counts.component s * m)
    (retained : Position → Fin 15)
    (hK : ∀ k,
      Fintype.card
          {t : Position // MME.DWZSquare.shapeZ (retained t) = k} =
        MME.DWZTable2Counts.alphaZ k * m)
    (small : MME.DWZTable2StandardForm.UsefulBlock m retained) :
    let K : Position → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained t)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let candidate : (Position → Fin 15) → Prop := fun w ↦
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Position → Fin 15 ↦ w)
        (fun t ↦ MME.DWZStep1Support.fineSplitGrade
          (small.1 t).1 (small.1 t).2) w
    let candidates : Finset (Position → Fin 15) := by
      classical
      exact T.filter candidate
    ((candidates.card : ℕ) : ℝ) ≤
      (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.card Outer : ℝ) *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.logAlphaP) := by
  classical
  dsimp only
  let K : Position → Fin 5 := fun t ↦
    MME.DWZSquare.shapeZ (retained t)
  let regionOfShape :
      Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
    if h : MME.DWZSquare.shapeX s = 0 ∨
        MME.DWZSquare.shapeY s = 0 then
      Sum.inl ⟨s, h⟩
    else
      Sum.inr (MME.DWZSquare.shapeZ s)
  let Outer :=
    {w : Position → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Position // w t = s} =
        MME.DWZTable2Counts.component s * m}
  let Typical :=
    {z : Position → Fin 3 × Fin 3 //
      (∀ t, MME.DWZTable2Counts.coarseOf (z t) = K t) ∧
      ∀ p, Fintype.card {t : Position // z t = p} =
        MME.DWZTable2Counts.gamma p * m}
  let Compatible : Outer → Typical → Prop := fun I z ↦
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (I.1 t) = r ∧ (z.1 t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a
  let candidate : (Position → Fin 15) → Prop := fun w ↦
    (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
    MME.DWZStep2Source.retainedFineCompatible m
      (fun w : Position → Fin 15 ↦ w)
      (fun t ↦ MME.DWZStep1Support.fineSplitGrade
        (small.1 t).1 (small.1 t).2) w
  let candidates : Finset (Position → Fin 15) := T.filter candidate
  have hsmallData :=
    mme_dwz_table2_useful_block_typical_and_compatible m retained small
  let smallT : Typical :=
    ⟨small.1,
      (by
        constructor
        · intro t
          simpa only [K] using small.2.1 t
        · exact hsmallData.1)⟩
  let Target := {I : Outer // Compatible I smallT}
  let C := candidates
  let embed : C → Target := fun w ↦ by
    have hw := Finset.mem_filter.mp w.2
    let I : Outer := ⟨w.1, hw.2.1, hTExact w.1 hw.1⟩
    refine ⟨I, ?_⟩
    have hcompat := hw.2.2
    simpa only [Compatible, smallT, regionOfShape,
      MME.DWZStep2Source.retainedFineCompatible,
      MME.DWZStep1Support.fineSplitLeft_encode] using hcompat
  have hembed : Function.Injective embed := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Target ↦ z.1.1) hxy
  have hcard : C.card ≤ Nat.card Target := by
    calc
      C.card = Fintype.card C := (Fintype.card_coe C).symm
      _ ≤ Fintype.card Target :=
        Fintype.card_le_of_injective embed hembed
      _ = Nat.card Target := Nat.card_eq_fintype_card.symm
  have hfixed :=
    mme_dwz_table2_compatible_outer_candidate_count_upper
      m K (by simpa only [K] using hK) smallT
  have hcardR : (C.card : ℝ) ≤ (Nat.card Target : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (by
    simpa only [K, Outer, Typical, Compatible, regionOfShape, smallT,
      Target, C, candidates, candidate] using hfixed)
