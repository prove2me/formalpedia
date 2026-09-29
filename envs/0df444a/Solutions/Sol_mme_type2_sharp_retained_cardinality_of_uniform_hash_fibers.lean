-- Prove2me | solution 1 for mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:18:53.195551+00:00
-- url     : https://prove2.me/submissions/aefa4351-def5-4a5f-8b12-cf301cc7579f

import Mathlib
import Theorems.Thm_mme_type2_uniform_hash_retention_aggregate_incidence
import Theorems.Thm_mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
import Theorems.Thm_mme_type2_induced_family_of_hash_collision_budget

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- Uniform one-edge and collision-pair hash fibers, together with a mode
degree bound and the exact target factorization, produce an induced family
with the sharp retained cardinality `V * loss`. -/
theorem solution
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q D Dstar : ℕ) (V loss : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll,
      (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (hedge : ∀ a ∈ targetAll,
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω a)).card = B * Q)
    (hpair : ∀ ab ∈ ((targetAll ×ˢ ambientAll).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)),
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω ab.1 ∧ retain ω ab.2)).card ≤ Q)
    (htargetAmbient : targetAll ⊆ ambientAll)
    (hclosure : ∀ ω,
      ∀ x ∈ targetAll.filter (retain ω),
      ∀ y ∈ targetAll.filter (retain ω),
      ∀ z ∈ targetAll.filter (retain ω),
        supportedMix x y z →
          ∃ e ∈ ambientAll.filter (retain ω),
            vertex 0 e = vertex 0 x ∧
            vertex 1 e = vertex 1 y ∧
            vertex 2 e = vertex 2 z)
    (hmargin :
      (P : ℝ) * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      V * loss ≤ (kept.card : ℝ) := by
  let target : State → Finset Edge := fun ω ↦ targetAll.filter (retain ω)
  let ambient : State → Finset Edge := fun ω ↦ ambientAll.filter (retain ω)
  obtain ⟨htargetIncidence, hcollisionIncidence⟩ :=
    mme_type2_uniform_hash_retention_aggregate_incidence
      vertex ambientAll targetAll retain B Q hedge hpair
  have hbudget :=
    mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
      vertex ambientAll targetAll ambient target P B Q D Dstar V loss
      hV hstate htargetCard hdegree
      (by simpa only [target] using htargetIncidence)
      (by simpa only [target, ambient] using hcollisionIncidence)
      hmargin
  have htarget : ∀ ω, target ω ⊆ ambient ω := by
    intro ω e he
    simp only [target, ambient, Finset.mem_filter] at he ⊢
    exact ⟨htargetAmbient he.1, he.2⟩
  have hclosure' : ∀ ω, ∀ x ∈ target ω, ∀ y ∈ target ω,
      ∀ z ∈ target ω, supportedMix x y z →
        ∃ e ∈ ambient ω,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z := by
    simpa only [target, ambient] using hclosure
  simpa only [target] using
    (mme_type2_induced_family_of_hash_collision_budget
      vertex supportedMix ambient target htarget hclosure' (V * loss) hbudget)
