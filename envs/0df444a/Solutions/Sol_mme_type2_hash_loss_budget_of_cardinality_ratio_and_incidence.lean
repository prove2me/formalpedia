-- Prove2me | solution 1 for mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:50:37.152822+00:00
-- url     : https://prove2.me/submissions/59b341b3-3582-446f-8f72-60ff89614a6f

import Mathlib

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem threeModeCollisionCard
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

theorem solution
    {State Edge : Type*} {Vertex : Fin 3 → Type*}
    [Fintype State] [DecidableEq Edge]
    [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (ambientAll targetAll : Finset Edge)
    (ambient target : State → Finset Edge)
    (P B Q D Dstar : ℕ) (V loss : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll,
      (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (htargetIncidence :
      ∑ ω, ((target ω).card : ℝ) =
        (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ))
    (hcollisionIncidence :
      ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        ((((targetAll ×ˢ ambientAll).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            vertex i p.1 = vertex i p.2)).card : ℝ) * (Q : ℝ)))
    (hmargin :
      (P : ℝ) * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (B : ℝ)) :
    (Fintype.card State : ℝ) * (V * loss) +
          ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ) ≤
      ∑ ω, ((target ω).card : ℝ) := by
  classical
  let globalCollisions := (targetAll ×ˢ ambientAll).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
  have hglobalNat : globalCollisions.card ≤ 3 * targetAll.card * D := by
    exact threeModeCollisionCard ambientAll targetAll vertex D hdegree
  have hglobalReal : (globalCollisions.card : ℝ) ≤
      3 * (targetAll.card : ℝ) * (D : ℝ) := by
    exact_mod_cast hglobalNat
  have hcollisionBound :
      ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        3 * (targetAll.card : ℝ) * (D : ℝ) * (Q : ℝ) := by
    calc
      ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            vertex i p.1 = vertex i p.2)).card : ℝ) ≤
          (globalCollisions.card : ℝ) * (Q : ℝ) := by
            simpa only [globalCollisions] using hcollisionIncidence
      _ ≤ (3 * (targetAll.card : ℝ) * (D : ℝ)) * (Q : ℝ) :=
        mul_le_mul_of_nonneg_right hglobalReal (by positivity)
  have hstateReal : (Fintype.card State : ℝ) =
      (P : ℝ) * (Q : ℝ) := by
    exact_mod_cast hstate
  have hscaled := mul_le_mul_of_nonneg_left hmargin
    (mul_nonneg hV (by positivity : (0 : ℝ) ≤ (Q : ℝ)))
  have harithmetic :
      (Fintype.card State : ℝ) * (V * loss) +
          3 * (targetAll.card : ℝ) * (D : ℝ) * (Q : ℝ) ≤
        (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ) := by
    rw [hstateReal, htargetCard]
    linarith [hscaled]
  calc
    (Fintype.card State : ℝ) * (V * loss) +
          ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        (Fintype.card State : ℝ) * (V * loss) +
          3 * (targetAll.card : ℝ) * (D : ℝ) * (Q : ℝ) :=
      by
        simpa only [add_comm] using
          add_le_add_left hcollisionBound
            ((Fintype.card State : ℝ) * (V * loss))
    _ ≤ (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ) := harithmetic
    _ = ∑ ω, ((target ω).card : ℝ) := htargetIncidence.symm
