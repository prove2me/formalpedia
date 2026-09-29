-- Prove2me | solution 1 for mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:41:28.683035+00:00
-- url     : https://prove2.me/submissions/ac214d26-7408-4893-8f8e-3e0bdf836548

import Theorems.Thm_mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Theorems.Thm_mme_bad_weight_card_mono_of_injective_candidate_map
import Definitions.Def_mme_dwz_retained_fine_compatibility

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Claim 6.8 on the global exact-profile family

The published collision estimate is stated on one fixed coarse-Z fiber.
The global first hash is instead applied to the full exact-profile family.
This theorem embeds the latter's same-Z competitors into the former while
preserving both fine compatibility and the conditioned second hash.
-/

/-- One useful block of one exact-profile owner inherits Claim 6.8's
one-eighth bad-weight estimate from its fixed-coarse-Z fiber.  The input
budget is the literal full-family candidate finset controlled by the global
common-prime theorem. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlevel : 4 < p)
    (retained : Fin (MME.DWZTable2Counts.scale * m) → Fin 15)
    (hretained : ∀ s,
      Fintype.card
          {t : Fin (MME.DWZTable2Counts.scale * m) // retained t = s} =
        MME.DWZTable2Counts.component s * m)
    (small : MME.DWZTable2StandardForm.UsefulBlock m retained)
    (b0 : ZMod p) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained t)
    let grade : Fin L → Fin (3 * 3) := fun t ↦
      MME.DWZStep1Support.fineSplitGrade
        (small.1 t).1 (small.1 t).2
    let fineCompatible : (Fin L → Fin 15) → Prop := fun w ↦
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) grade w
    let candidates : Finset (Fin L → Fin 15) := by
      classical
      exact T.filter (fun w ↦ sameZ w ∧ fineCompatible w)
    let GlobalOuter := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
    let addressX : GlobalOuter → Fin (n + 1) → Fin 5 := fun w t ↦
      MME.DWZSquare.shapeX (w.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w X ↦
      b0 + ∑ t, ((X t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t,
        (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
          ZMod p) * w t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
    let hashRetained : GlobalOuter →
        (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
      hX w (addressX A) = hZ (conditionedW0 w) w addressZ
    let bad : Finset (Fin (n + 1) → ZMod p) := by
      classical
      exact Finset.univ.filter (fun w ↦
        1 < (Finset.univ.filter (fun A : GlobalOuter ↦
          fineCompatible A.1 ∧ hashRetained A w)).card)
    8 * candidates.card ≤ p →
      8 * bad.card ≤
        Fintype.card (Fin (n + 1) → ZMod p) := by
  classical
  dsimp only
  intro hbudget
  let L := MME.DWZTable2Counts.scale * m
  let n := L - 1
  let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
    dsimp only [n, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t : Fin L // w t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin L → Fin 15) := Finset.univ.filter ExactProfile
  let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ t, MME.DWZSquare.shapeZ (w t) =
      MME.DWZSquare.shapeZ (retained t)
  let grade : Fin L → Fin (3 * 3) := fun t ↦
    MME.DWZStep1Support.fineSplitGrade (small.1 t).1 (small.1 t).2
  let fineCompatible : (Fin L → Fin 15) → Prop := fun w ↦
    MME.DWZStep2Source.retainedFineCompatible m
      (fun w : Fin L → Fin 15 ↦ w) grade w
  let candidates : Finset (Fin L → Fin 15) :=
    T.filter (fun w ↦ sameZ w ∧ fineCompatible w)
  let GlobalOuter := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
  let K : Fin L → Fin 5 := fun t ↦ MME.DWZSquare.shapeZ (retained t)
  let FixedOuter :=
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧ ExactProfile w}
  let regionOfShape :
      Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
    if h : MME.DWZSquare.shapeX s = 0 ∨
        MME.DWZSquare.shapeY s = 0 then
      Sum.inl ⟨s, h⟩
    else
      Sum.inr (MME.DWZSquare.shapeZ s)
  let Typical :=
    {z : Fin L → Fin 3 × Fin 3 //
      (∀ t, MME.DWZTable2Counts.coarseOf (z t) = K t) ∧
      ∀ q, Fintype.card {t : Fin L // z t = q} =
        MME.DWZTable2Counts.gamma q * m}
  let Compatible : FixedOuter → Typical → Prop := fun I z ↦
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Fin L // regionOfShape (I.1 t) = r ∧ (z.1 t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a
  have hsmallData :=
    mme_dwz_table2_useful_block_typical_and_compatible m retained small
  let smallT : Typical :=
    ⟨small.1,
      (by
        constructor
        · intro t
          exact small.2.1 t
        · exact hsmallData.1)⟩
  let retainedF : FixedOuter := ⟨retained, fun _ ↦ rfl, hretained⟩
  have hcompat_iff (A : FixedOuter) :
      fineCompatible A.1 ↔ Compatible A smallT := by
    simp only [fineCompatible, Compatible, smallT, regionOfShape, grade,
      MME.DWZStep2Source.retainedFineCompatible,
      MME.DWZStep1Support.fineSplitLeft_encode]
  let fixedCandidates : Finset FixedOuter :=
    Finset.univ.filter (fun A ↦ A ≠ retainedF ∧ Compatible A smallT)
  let embedCandidate : {A // A ∈ fixedCandidates} →
      {w // w ∈ candidates} := fun A ↦ by
    have hA := (Finset.mem_filter.mp A.2).2
    refine ⟨A.1.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        ExactProfile]
      exact A.1.2.2
    · exact ⟨A.1.2.1, (hcompat_iff A.1).2 hA.2⟩
  have hembedCandidate : Function.Injective embedCandidate := by
    intro A B hAB
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x ↦ x.1) hAB
  have hfixedCard : fixedCandidates.card ≤ candidates.card := by
    calc
      fixedCandidates.card = Fintype.card {A // A ∈ fixedCandidates} :=
        (Fintype.card_coe fixedCandidates).symm
      _ ≤ Fintype.card {w // w ∈ candidates} :=
        Fintype.card_le_of_injective embedCandidate hembedCandidate
      _ = candidates.card := Fintype.card_coe candidates
  have hfixedBudget : 8 * fixedCandidates.card ≤ p :=
    (Nat.mul_le_mul_left 8 hfixedCard).trans hbudget
  let addressXG : GlobalOuter → Fin (n + 1) → Fin 5 := fun w t ↦
    MME.DWZSquare.shapeX (w.1 (reindex t))
  let addressXF : FixedOuter → Fin (n + 1) → Fin 5 := fun w t ↦
    MME.DWZSquare.shapeX (w.1 (reindex t))
  let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
  let hX : (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p := fun w X ↦
    b0 + ∑ t, ((X t).val : ZMod p) * w t
  let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
      (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
    b0 + (2 : ZMod p)⁻¹ *
      (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
  let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
    2 * (∑ t, ((addressXF retainedF t).val : ZMod p) * w t) -
      ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
  let hashG : GlobalOuter → (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
    hX w (addressXG A) = hZ (conditionedW0 w) w addressZ
  let hashF : FixedOuter → (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
    hX w (addressXF A) = hZ (conditionedW0 w) w addressZ
  have hfixedBad :=
    mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
      m hm K hpodd hlevel b0 retainedF smallT
        (by simpa only [Compatible, smallT, regionOfShape] using hsmallData.2)
        (by simpa only [fixedCandidates] using hfixedBudget)
  let embed : GlobalOuter → FixedOuter := fun A ↦ by
    refine ⟨A.1, A.2.2, ?_⟩
    exact (Finset.mem_filter.mp A.2.1).2
  have hembed : Function.Injective embed := by
    intro A B hAB
    apply Subtype.ext
    exact congrArg (fun x ↦ x.1) hAB
  have hrel : ∀ A w,
      (fineCompatible A.1 ∧ hashG A w) →
        (Compatible (embed A) smallT ∧ hashF (embed A) w) := by
    intro A w hA
    exact ⟨(hcompat_iff (embed A)).1 hA.1, hA.2⟩
  have hmono := mme_bad_weight_card_mono_of_injective_candidate_map
    (fun A : GlobalOuter ↦ fun w : Fin (n + 1) → ZMod p ↦
      fineCompatible A.1 ∧ hashG A w)
    (fun A : FixedOuter ↦ fun w : Fin (n + 1) → ZMod p ↦
      Compatible A smallT ∧ hashF A w)
    embed hembed hrel
  exact (Nat.mul_le_mul_left 8 hmono).trans (by
    simpa only [L, n, reindex, K, FixedOuter, Typical, Compatible,
      regionOfShape, smallT, retainedF, addressXF, addressZ, hX, hZ,
      conditionedW0, hashF] using hfixedBad)
