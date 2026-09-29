-- Prove2me | solution 1 for mme_dwz_target_two_mode_collision_card_le_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:03:19.95114+00:00
-- url     : https://prove2.me/submissions/bc54b290-d600-471f-910f-4b945aa43400

import Mathlib

set_option autoImplicit false
set_option warningAsError true

/-!
# Target-relative two-mode collision count

This is the deterministic counting step in the asymmetric hash.  The first
edge of a directed collision is required to lie in the chosen joint-profile
family `T`, while the second may be any edge in the full marginal family
`A`.  Thus the bound scales with `T.card`, not `A.card`.
-/

theorem solution
    {Edge X Y : Type}
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y) (d : ℕ)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d) :
    ((T.product A).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        2 * T.card * d := by
  classical
  let CX := (T.product A).filter (fun p ↦ x p.1 = x p.2)
  let CY := (T.product A).filter (fun p ↦ y p.1 = y p.2)
  let FX : Edge → Finset (Edge × Edge) := fun a ↦
    (A.filter (fun b ↦ x b = x a)).image (fun b ↦ (a, b))
  let FY : Edge → Finset (Edge × Edge) := fun a ↦
    (A.filter (fun b ↦ y b = y a)).image (fun b ↦ (a, b))
  have hCX : CX = T.biUnion FX := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpProd := Finset.mem_product.mp hp'.1
      refine Finset.mem_biUnion.mpr ⟨p.1, hpProd.1, ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,
        Finset.mem_filter.mpr ⟨hpProd.2, hp'.2.symm⟩, rfl⟩
    · intro hp
      obtain ⟨a, haT, hpFX⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨b, hb, hpab⟩ := Finset.mem_image.mp hpFX
      rw [← hpab]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨haT, (Finset.mem_filter.mp hb).1⟩,
          (Finset.mem_filter.mp hb).2.symm⟩
  have hCY : CY = T.biUnion FY := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpProd := Finset.mem_product.mp hp'.1
      refine Finset.mem_biUnion.mpr ⟨p.1, hpProd.1, ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,
        Finset.mem_filter.mpr ⟨hpProd.2, hp'.2.symm⟩, rfl⟩
    · intro hp
      obtain ⟨a, haT, hpFY⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨b, hb, hpab⟩ := Finset.mem_image.mp hpFY
      rw [← hpab]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨haT, (Finset.mem_filter.mp hb).1⟩,
          (Finset.mem_filter.mp hb).2.symm⟩
  have hFX : ∀ a ∈ T, (FX a).card ≤ d := by
    intro a ha
    calc
      (FX a).card ≤ (A.filter (fun b ↦ x b = x a)).card :=
        Finset.card_image_le
      _ ≤ d := hx a ha
  have hFY : ∀ a ∈ T, (FY a).card ≤ d := by
    intro a ha
    calc
      (FY a).card ≤ (A.filter (fun b ↦ y b = y a)).card :=
        Finset.card_image_le
      _ ≤ d := hy a ha
  have hCXcard : CX.card ≤ T.card * d := by
    rw [hCX]
    exact Finset.card_biUnion_le_card_mul T FX d hFX
  have hCYcard : CY.card ≤ T.card * d := by
    rw [hCY]
    exact Finset.card_biUnion_le_card_mul T FY d hFY
  have hsub :
      (T.product A).filter (fun p ↦
        p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2)) ⊆ CX ∪ CY := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    rcases hp'.2.2 with hpx | hpy
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp'.1, hpy⟩)
  calc
    ((T.product A).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card
        ≤ (CX ∪ CY).card := Finset.card_le_card hsub
    _ ≤ CX.card + CY.card := Finset.card_union_le CX CY
    _ ≤ T.card * d + T.card * d := Nat.add_le_add hCXcard hCYcard
    _ = 2 * T.card * d := by ring
