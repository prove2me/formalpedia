-- Prove2me | solution 1 for mme_target_ambient_three_mode_collision_card_le_of_fiber_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:45:55.722483+00:00
-- url     : https://prove2.me/submissions/eb3e2f77-c71b-41e8-adcc-c74e7442e0a8

import Mathlib

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (ambient target : Finset Edge)
    (vertex : ∀ i, Edge → Vertex i) (D : ℕ)
    (hdeg : ∀ i : Fin 3, ∀ a ∈ target,
      (ambient.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D) :
    (((target ×ˢ ambient).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3,
        vertex i p.1 = vertex i p.2)).card) ≤
      3 * target.card * D := by
  classical
  let star (i : Fin 3) (a : Edge) :=
    ambient.filter (fun b ↦ vertex i b = vertex i a)
  let collisions := (target ×ˢ ambient).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
  let collisionsAt (i : Fin 3) := target.biUnion (fun a ↦
    (star i a).image (fun b ↦ (a, b)))
  let collisionUnion :=
    (Finset.univ : Finset (Fin 3)).biUnion collisionsAt
  have hsubset : collisions ⊆ collisionUnion := by
    intro ab hab
    have hfull := hab
    simp only [collisions, Finset.mem_filter, Finset.mem_product] at hfull
    obtain ⟨⟨ha, hb⟩, _hne, i, hi⟩ := hfull
    simp only [collisionUnion, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    refine ⟨i, ?_⟩
    simp only [collisionsAt, Finset.mem_biUnion]
    refine ⟨ab.1, ha, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨ab.2, ?_, rfl⟩
    simp only [star, Finset.mem_filter]
    exact ⟨hb, hi.symm⟩
  calc
    collisions.card ≤ collisionUnion.card := Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 3, (collisionsAt i).card := by
      simpa only [collisionUnion] using (Finset.card_biUnion_le :
        collisionUnion.card ≤
          ∑ i ∈ (Finset.univ : Finset (Fin 3)),
            (collisionsAt i).card)
    _ ≤ ∑ i : Fin 3, ∑ a ∈ target, (star i a).card := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        (collisionsAt i).card ≤ ∑ a ∈ target,
            ((star i a).image (fun b ↦ (a, b))).card := by
          simpa only [collisionsAt] using (Finset.card_biUnion_le :
            (target.biUnion (fun a ↦
              (star i a).image (fun b ↦ (a, b)))).card ≤
              ∑ a ∈ target,
                ((star i a).image (fun b ↦ (a, b))).card)
        _ ≤ ∑ a ∈ target, (star i a).card := by
          apply Finset.sum_le_sum
          intro a _ha
          exact Finset.card_image_le
    _ ≤ ∑ i : Fin 3, ∑ a ∈ target, D := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro a ha
      exact hdeg i a ha
    _ = 3 * target.card * D := by simp [mul_assoc]
