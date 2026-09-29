-- Prove2me | solution 1 for mme_bad_weight_card_mono_of_injective_candidate_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:02:41.816462+00:00
-- url     : https://prove2.me/submissions/83f443f6-b243-47a1-9c76-20ac615c3fc5

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Small Big Weight : Type*}
    [Fintype Small] [DecidableEq Small]
    [Fintype Big] [DecidableEq Big]
    [Fintype Weight] [DecidableEq Weight]
    (smallRel : Small → Weight → Prop) [DecidableRel smallRel]
    (bigRel : Big → Weight → Prop) [DecidableRel bigRel]
    (f : Small → Big) (hf : Function.Injective f)
    (hrel : ∀ a w, smallRel a w → bigRel (f a) w) :
    (Finset.univ.filter (fun w : Weight ↦
      1 < (Finset.univ.filter (fun a : Small ↦ smallRel a w)).card)).card ≤
    (Finset.univ.filter (fun w : Weight ↦
      1 < (Finset.univ.filter (fun b : Big ↦ bigRel b w)).card)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  let smallFiber : Finset Small :=
    Finset.univ.filter (fun a ↦ smallRel a w)
  let bigFiber : Finset Big :=
    Finset.univ.filter (fun b ↦ bigRel b w)
  let embed : ↥smallFiber → ↥bigFiber := fun a ↦
    ⟨f a.1, by
      simp only [bigFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      apply hrel a.1 w
      simpa only [smallFiber, Finset.mem_filter, Finset.mem_univ,
        true_and] using a.2⟩
  have hembed : Function.Injective embed := by
    intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  have hcard : smallFiber.card ≤ bigFiber.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective embed hembed
  exact hw.trans_le hcard
