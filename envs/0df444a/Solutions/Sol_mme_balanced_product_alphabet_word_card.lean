-- Prove2me | solution 1 for mme_balanced_product_alphabet_word_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:47:43.663945+00:00
-- url     : https://prove2.me/submissions/56ce8e9e-e775-4d53-8713-25ae5b8d44f1

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Data.Finite.Card

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZBalancedProductAlphabet

private noncomputable def wordEquiv
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V m : ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    {w : PowIndex I (H * m) //
      ∀ h, Fintype.card
          {r : Fin (H * m) // grade (PowIndex.get _ w r) = h} = m} ≃
      ({g : Fin (H * m) → Fin H //
        ∀ h, Fintype.card {r : Fin (H * m) // g r = h} = m} ×
        (Fin (H * m) → Fin V)) where
  toFun w :=
    (⟨fun r ↦ (letter (PowIndex.get _ w.1 r)).1, by
      intro h
      have hw := w.2 h
      have htypes :
          {r : Fin (H * m) //
              (letter (PowIndex.get (H * m) w.1 r)).1 = h} =
            {r : Fin (H * m) //
              grade (PowIndex.get (H * m) w.1 r) = h} := by
        congr 1
        funext r
        apply propext
        rw [hletter]
      simpa only [htypes] using hw⟩,
      fun r ↦ (letter (PowIndex.get _ w.1 r)).2)
  invFun gv :=
    ⟨PowIndex.ofFun (H * m)
        (fun r ↦ letter.symm (gv.1.1 r, gv.2 r)), by
      intro h
      have hg := gv.1.2 h
      have htypes :
          {r : Fin (H * m) //
              grade (PowIndex.get (H * m)
                (PowIndex.ofFun (H * m)
                  (fun r ↦ letter.symm (gv.1.1 r, gv.2 r))) r) = h} =
            {r : Fin (H * m) // gv.1.1 r = h} := by
        congr 1
        funext r
        apply propext
        simp only [PowIndex.get_ofFun, hletter,
          Equiv.apply_symm_apply]
      simpa only [htypes] using hg⟩
  left_inv w := by
    apply Subtype.ext
    apply (PowIndex.equivFun I (H * m)).injective
    funext r
    simp only [PowIndex.equivFun, Equiv.coe_fn_mk, PowIndex.get_ofFun]
    rw [show
      ((letter (PowIndex.get (H * m) w.1 r)).1,
          (letter (PowIndex.get (H * m) w.1 r)).2) =
        letter (PowIndex.get (H * m) w.1 r) by
          exact Prod.eta _]
    exact letter.symm_apply_apply _
  right_inv gv := by
    rcases gv with ⟨g, v⟩
    apply Prod.ext
    · apply Subtype.ext
      funext r
      simp only [PowIndex.get_ofFun, Equiv.apply_symm_apply]
    · funext r
      simp only [PowIndex.get_ofFun, Equiv.apply_symm_apply]

/-- Exact cardinality of balanced words over an alphabet presented as a
grade and an independent within-grade coordinate. -/
theorem balanced_product_alphabet_word_card
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V m : ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    Nat.card
        {w : PowIndex I (H * m) //
          ∀ h, Fintype.card
              {r : Fin (H * m) // grade (PowIndex.get _ w r) = h} = m} =
      Nat.card
          {g : Fin (H * m) → Fin H //
            ∀ h, Fintype.card {r : Fin (H * m) // g r = h} = m} *
        V ^ (H * m) := by
  rw [Nat.card_congr (wordEquiv H V m grade letter hletter)]
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]

end MME.DWZBalancedProductAlphabet

/-- Exact cardinality of balanced words over an alphabet presented as a
grade and an independent within-grade coordinate. -/
theorem mme_balanced_product_alphabet_word_card
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V m : ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    Nat.card
        {w : MME.DWZComponentRestriction.PowIndex I (H * m) //
          ∀ h, Fintype.card
              {r : Fin (H * m) // grade
                (MME.DWZComponentRestriction.PowIndex.get _ w r) = h} = m} =
      Nat.card
          {g : Fin (H * m) → Fin H //
            ∀ h, Fintype.card {r : Fin (H * m) // g r = h} = m} *
        V ^ (H * m) :=
  MME.DWZBalancedProductAlphabet.balanced_product_alphabet_word_card
    H V m grade letter hletter

theorem solution
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V m : ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    Nat.card
        {w : MME.DWZComponentRestriction.PowIndex I (H * m) //
          ∀ h, Fintype.card
              {r : Fin (H * m) // grade
                (MME.DWZComponentRestriction.PowIndex.get _ w r) = h} = m} =
      Nat.card
          {g : Fin (H * m) → Fin H //
            ∀ h, Fintype.card {r : Fin (H * m) // g r = h} = m} *
        V ^ (H * m) :=
  mme_balanced_product_alphabet_word_card H V m grade letter hletter
