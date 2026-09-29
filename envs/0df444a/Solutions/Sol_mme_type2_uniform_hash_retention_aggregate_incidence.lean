-- Prove2me | solution 1 for mme_type2_uniform_hash_retention_aggregate_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:02:33.70653+00:00
-- url     : https://prove2.me/submissions/7de0e2d8-60f3-4a26-962a-120880b39b10

import Mathlib
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [DecidableEq State] [DecidableEq Edge]
    [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (B Q : ℕ)
    (hedge : ∀ a ∈ targetAll,
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω a)).card = B * Q)
    (hpair : ∀ ab ∈ ((targetAll ×ˢ ambientAll).filter (fun p ↦
        p.1 ≠ p.2 ∧ ∃ i : Fin 3,
          vertex i p.1 = vertex i p.2)),
      ((Finset.univ : Finset State).filter (fun ω ↦
        retain ω ab.1 ∧ retain ω ab.2)).card ≤ Q) :
    (∑ ω, (((targetAll.filter (retain ω)).card : ℝ))) =
        (targetAll.card : ℝ) * (B : ℝ) * (Q : ℝ) ∧
      (∑ ω, (((((targetAll.filter (retain ω)) ×ˢ
          (ambientAll.filter (retain ω))).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ))) ≤
        ((((targetAll ×ˢ ambientAll).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            vertex i p.1 = vertex i p.2)).card : ℝ) * (Q : ℝ)) := by
  classical
  let collisions := (targetAll ×ˢ ambientAll).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
  have hgoodNat :
      (∑ ω, (targetAll.filter (retain ω)).card) =
        targetAll.card * B * Q := by
    calc
      (∑ ω, (targetAll.filter (retain ω)).card) =
          ∑ a ∈ targetAll,
            ((Finset.univ : Finset State).filter
              (fun ω ↦ retain ω a)).card := by
        simpa only using
          (mme_finset_incidence_double_count
            (Finset.univ : Finset State) targetAll retain)
      _ = ∑ a ∈ targetAll, B * Q := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hedge a ha
      _ = targetAll.card * B * Q := by simp [mul_assoc]
  have hcollisionAt (ω : State) :
      (((targetAll.filter (retain ω)) ×ˢ
          (ambientAll.filter (retain ω))).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)) =
        collisions.filter (fun ab ↦
          retain ω ab.1 ∧ retain ω ab.2) := by
    ext ab
    simp only [collisions, Finset.mem_filter, Finset.mem_product]
    tauto
  have hbadNat :
      (∑ ω, ((((targetAll.filter (retain ω)) ×ˢ
          (ambientAll.filter (retain ω))).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card)) ≤
        collisions.card * Q := by
    calc
      (∑ ω, ((((targetAll.filter (retain ω)) ×ˢ
          (ambientAll.filter (retain ω))).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card)) =
          ∑ ω, (collisions.filter (fun ab ↦
            retain ω ab.1 ∧ retain ω ab.2)).card := by
        apply Finset.sum_congr rfl
        intro ω _hω
        rw [hcollisionAt]
      _ = ∑ ab ∈ collisions,
          ((Finset.univ : Finset State).filter (fun ω ↦
            retain ω ab.1 ∧ retain ω ab.2)).card := by
        simpa only using
          (mme_finset_incidence_double_count
            (Finset.univ : Finset State) collisions
              (fun ω ab ↦ retain ω ab.1 ∧ retain ω ab.2))
      _ ≤ ∑ ab ∈ collisions, Q := by
        apply Finset.sum_le_sum
        intro ab hab
        exact hpair ab (by simpa only [collisions] using hab)
      _ = collisions.card * Q := by simp
  constructor
  · exact_mod_cast hgoodNat
  · have hbadReal :
        (∑ ω, (((((targetAll.filter (retain ω)) ×ˢ
            (ambientAll.filter (retain ω))).filter (fun p ↦
              p.1 ≠ p.2 ∧ ∃ i : Fin 3,
                vertex i p.1 = vertex i p.2)).card : ℝ))) ≤
          (collisions.card : ℝ) * (Q : ℝ) := by
      exact_mod_cast hbadNat
    simpa only [collisions] using hbadReal
