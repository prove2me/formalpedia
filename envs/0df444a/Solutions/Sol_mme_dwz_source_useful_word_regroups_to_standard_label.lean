-- Prove2me | solution 1 for mme_dwz_source_useful_word_regroups_to_standard_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:50:18.754421+00:00
-- url     : https://prove2.me/submissions/96142447-3bf0-46b1-9a5b-01fa3903dc80

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

namespace MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

/-- Restrict an arbitrary outer-preserving position equivalence to one
Table-2 component fiber. -/
noncomputable def groupedComponentFiberEquiv
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (s : Fin 15) :
    Fin (DWZTable2Counts.component s * m) ≃
      {r : Fin N // outer r = s} := by
  let f : Fin (DWZTable2Counts.component s * m) →
      {r : Fin N // outer r = s} := fun r ↦
    ⟨e ⟨s, r⟩, he ⟨s, r⟩⟩
  have hf : Function.Injective f := by
    intro r r' h
    have hsigma : (⟨s, r⟩ :
        DWZComponentRestriction.GroupedPosition m) = ⟨s, r'⟩ :=
      e.injective (congrArg Subtype.val h)
    cases hsigma
    rfl
  have hcard :
      Fintype.card (Fin (DWZTable2Counts.component s * m)) =
        Fintype.card {r : Fin N // outer r = s} := by
    simpa using (houter s).symm
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩)

/-- Reindex one source-order canonical coarse-Z letter into a fixed grouped
component fiber. -/
noncomputable def groupedSourceLetter
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer) (s : Fin 15)
    (r : Fin (DWZTable2Counts.component s * m)) :
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (DWZSquare.shapeZ s) := by
  let q := groupedComponentFiberEquiv outer houter e he s r
  have hshape : DWZSquare.shapeZ (outer q.1) =
      DWZSquare.shapeZ s := congrArg DWZSquare.shapeZ q.2
  exact hshape ▸ W q.1

private theorem liftedCoarsePair_leftGrade_cast
    {c d : Fin 5} (h : c = d)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6 c) :
    (h ▸ x).leftGrade = x.leftGrade := by
  cases h
  rfl

private theorem liftedCoarsePair_rightGrade_cast
    {c d : Fin 5} (h : c = d)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6 c) :
    (h ▸ x).rightGrade = x.rightGrade := by
  cases h
  rfl

theorem groupedSourceLetter_leftGrade
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer) (s : Fin 15)
    (r : Fin (DWZTable2Counts.component s * m)) :
    (groupedSourceLetter houter e he W s r).leftGrade =
      (W (groupedComponentFiberEquiv outer houter e he s r).1).leftGrade := by
  unfold groupedSourceLetter
  dsimp only
  exact liftedCoarsePair_leftGrade_cast _ _

theorem groupedSourceLetter_rightGrade
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer) (s : Fin 15)
    (r : Fin (DWZTable2Counts.component s * m)) :
    (groupedSourceLetter houter e he W s r).rightGrade =
      (W (groupedComponentFiberEquiv outer houter e he s r).1).rightGrade := by
  unfold groupedSourceLetter
  dsimp only
  exact liftedCoarsePair_rightGrade_cast _ _

/-- A useful canonical source Z word becomes an available grouped component
word in every Table-2 row. -/
noncomputable def sourceWordToGroupedAllowed
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer) (hW : addressWordUseful m outer W) :
    DWZComponentRestriction.GroupedAllowedWords.{u} m := by
  intro s
  refine ⟨DWZComponentRestriction.PowIndex.ofFun _
      (groupedSourceLetter houter e he W s), ?_⟩
  intro a
  let fiber := groupedComponentFiberEquiv outer houter e he s
  let gradeEquiv :
      {r : Fin (DWZTable2Counts.component s * m) //
        (groupedSourceLetter houter e he W s r).leftGrade = a} ≃
      {q : Fin N // outer q = s ∧ (W q).leftGrade = a} :=
    { toFun := fun r ↦ ⟨(fiber r.1).1,
          ⟨(fiber r.1).2, by
            simpa only [groupedSourceLetter_leftGrade] using r.2⟩⟩
      invFun := fun q ↦ ⟨fiber.symm ⟨q.1, q.2.1⟩, by
          rw [groupedSourceLetter_leftGrade]
          have happ :
              groupedComponentFiberEquiv outer houter e he s
                  (fiber.symm ⟨q.1, q.2.1⟩) = ⟨q.1, q.2.1⟩ := by
            change fiber (fiber.symm ⟨q.1, q.2.1⟩) = ⟨q.1, q.2.1⟩
            exact fiber.apply_symm_apply _
          rw [happ]
          exact q.2.2⟩
      left_inv := fun r ↦ by apply Subtype.ext; simp
      right_inv := fun q ↦ by apply Subtype.ext; simp }
  rw [DWZComponentRestriction.PowIndex.get_ofFun]
  exact (Fintype.card_congr gradeEquiv).trans (hW s a)

/-- Regrouping preserves the literal fine pair read at every position. -/
theorem groupedFineZ_sourceWordToGroupedAllowed
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer) (hW : addressWordUseful m outer W)
    (p : DWZComponentRestriction.GroupedPosition m) :
    DWZComponentRestriction.groupedFineZ
        (sourceWordToGroupedAllowed houter e he W hW) p =
      addressFineZ W (e p) := by
  rcases p with ⟨s, r⟩
  unfold DWZComponentRestriction.groupedFineZ
  dsimp only [sourceWordToGroupedAllowed]
  rw [DWZComponentRestriction.PowIndex.get_ofFun]
  change
    ((groupedSourceLetter houter e he W s r).leftGrade,
      (groupedSourceLetter houter e he W s r).rightGrade) =
    ((W (e ⟨s, r⟩)).leftGrade, (W (e ⟨s, r⟩)).rightGrade)
  rw [groupedSourceLetter_leftGrade, groupedSourceLetter_rightGrade]
  have hfiber :
      (groupedComponentFiberEquiv outer houter e he s r).1 = e ⟨s, r⟩ :=
    rfl
  rw [hfiber]

/-- A useful source Z word becomes a grouped available word whose literal
standard-block label is exactly the transported source useful block. -/
theorem sourceUsefulWord_regroups_to_standard_label
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (blockEquiv : DWZTable2StandardForm.UsefulBlock m outer ≃
      DWZComponentRestriction.DWZStandardBlock m)
    (hblock : ∀ small p,
      (blockEquiv small).1 p = small.1 (e p))
    (W : AddressZWord.{u} outer) (hW : addressWordUseful m outer W) :
    ∃ Wg : DWZComponentRestriction.GroupedAllowedWords.{u} m,
      (∀ p, DWZComponentRestriction.groupedFineZ Wg p =
        addressFineZ W (e p)) ∧
      DWZComponentRestriction.groupedUsefulBlock m Wg =
        blockEquiv (addressUsefulBlock m outer W hW) := by
  let Wg : DWZComponentRestriction.GroupedAllowedWords.{u} m :=
    sourceWordToGroupedAllowed houter e he W hW
  refine ⟨Wg, groupedFineZ_sourceWordToGroupedAllowed
    houter e he W hW, ?_⟩
  apply Subtype.ext
  funext p
  rw [hblock]
  change DWZComponentRestriction.groupedFineZ Wg p =
    addressFineZ W (e p)
  exact groupedFineZ_sourceWordToGroupedAllowed houter e he W hW p

end MME.DWZSourceAligned

theorem solution
    {N m : ℕ} {outer : Fin N → Fin 15}
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      MME.DWZComponentRestriction.groupedOuter p)
    (blockEquiv : MME.DWZTable2StandardForm.UsefulBlock m outer ≃
      MME.DWZComponentRestriction.DWZStandardBlock m)
    (hblock : ∀ small p,
      (blockEquiv small).1 p = small.1 (e p))
    (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
    (hW : MME.DWZSourceAligned.addressWordUseful m outer W) :
    ∃ Wg : MME.DWZComponentRestriction.GroupedAllowedWords.{u} m,
      (∀ p, MME.DWZComponentRestriction.groupedFineZ Wg p =
        MME.DWZSourceAligned.addressFineZ W (e p)) ∧
      MME.DWZComponentRestriction.groupedUsefulBlock m Wg =
        blockEquiv
          (MME.DWZSourceAligned.addressUsefulBlock m outer W hW) := by
  exact MME.DWZSourceAligned.sourceUsefulWord_regroups_to_standard_label
    houter e he blockEquiv hblock W hW
