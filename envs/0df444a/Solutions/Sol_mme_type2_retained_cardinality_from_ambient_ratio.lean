-- Prove2me | solution 1 for mme_type2_retained_cardinality_from_ambient_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:31.770118+00:00
-- url     : https://prove2.me/submissions/49ddea8d-6d31-4757-b3a3-d2f0402ae942

import Mathlib

set_option autoImplicit false

namespace AmbientRatioProof

-- Accepted source by marwahaha; submission d282eef3-2837-469a-933a-c5a3d2285f05.
namespace RetainedDependency0
open BigOperators

set_option autoImplicit false

/-- Double-count a finite incidence relation by its two projections. -/
theorem mme_finset_incidence_double_count
    {Ω A : Type} [DecidableEq Ω] [DecidableEq A]
    (W : Finset Ω) (U : Finset A) (P : Ω → A → Prop)
    [DecidableRel P] :
    (∑ ω ∈ W, (U.filter (P ω)).card) =
      ∑ a ∈ U, (W.filter (fun ω => P ω a)).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm
end RetainedDependency0
export RetainedDependency0 (mme_finset_incidence_double_count)

-- Accepted source by marwahaha; submission 7de0e2d8-60f3-4a26-962a-120880b39b10.
namespace RetainedDependency1
open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem mme_type2_uniform_hash_retention_aggregate_incidence
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
end RetainedDependency1
export RetainedDependency1 (mme_type2_uniform_hash_retention_aggregate_incidence)

-- Accepted source by marwahaha; submission 59b341b3-3582-446f-8f72-60ff89614a6f.
namespace RetainedDependency2
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

theorem mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
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
end RetainedDependency2
export RetainedDependency2 (mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence)

-- Accepted source by marwahaha; submission 03d1f9d8-3c13-472c-9a15-888ae5129f8c.
namespace RetainedDependency3
open BigOperators

set_option autoImplicit false

/-- A real-valued version of finite collision-budget averaging.  This avoids
rounding a real target loss before selecting the favorable hash state. -/
theorem mme_finite_collision_budget_averaging_real {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (good bad : Ω → ℕ) (L : ℝ)
    (hbudget :
      (Fintype.card Ω : ℝ) * L + ∑ ω, (bad ω : ℝ) ≤
        ∑ ω, (good ω : ℝ)) :
    ∃ ω, (bad ω : ℝ) + L ≤ (good ω : ℝ) := by
  by_contra hnone
  push_neg at hnone
  have hsum :
      (∑ ω, (good ω : ℝ)) < ∑ ω, ((bad ω : ℝ) + L) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun ω _ => hnone ω)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsum' :
      (∑ ω, (good ω : ℝ)) <
        (Fintype.card Ω : ℝ) * L + ∑ ω, (bad ω : ℝ) := by
    simpa only [mul_comm, add_comm] using hsum
  exact (not_lt_of_ge hbudget) hsum'
end RetainedDependency3
export RetainedDependency3 (mme_finite_collision_budget_averaging_real)

-- Accepted source by marwahaha; submission 6a689c95-606a-4a66-83f9-b025123b65f2.
namespace RetainedDependency4
set_option autoImplicit false

/-- Delete precisely those target edges which collide with any edge of the
ambient hypergraph.  The surviving target edges form a matching which is
vertex-induced relative to the whole ambient edge set. -/
theorem mme_tripartite_target_isolation_pruning
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (v : ∀ i, Edge → Vertex i) (E T : Finset Edge) (hTE : T ⊆ E) :
    let C := (T ×ˢ E).filter (fun p =>
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
    ∃ F : Finset Edge,
      F ⊆ T ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y →
        ∀ i : Fin 3, v i x ≠ v i y) ∧
      (∀ e ∈ E,
        (∀ i : Fin 3, ∃ f ∈ F, v i e = v i f) → e ∈ F) ∧
      T.card ≤ F.card + C.card := by
  classical
  dsimp only
  let C : Finset (Edge × Edge) := (T ×ˢ E).filter (fun p =>
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)
  let bad : Finset Edge := C.image Prod.fst
  let F : Finset Edge := T \ bad
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact Finset.sdiff_subset
  · intro x hx y hy hxy i hvi
    have hxT : x ∈ T := Finset.sdiff_subset hx
    have hyE : y ∈ E := hTE (Finset.sdiff_subset hy)
    have hpair : (x, y) ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxT, hyE⟩, hxy, ⟨i, hvi⟩⟩
    have hxbad : x ∈ bad :=
      Finset.mem_image.mpr ⟨(x, y), hpair, rfl⟩
    exact (Finset.mem_sdiff.mp hx).2 hxbad
  · intro e heE hvertices
    obtain ⟨f, hfF, hef⟩ := hvertices (0 : Fin 3)
    by_cases hfe : f = e
    · simpa only [hfe] using hfF
    · have hfT : f ∈ T := Finset.sdiff_subset hfF
      have hpair : (f, e) ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hfT, heE⟩, hfe, ⟨(0 : Fin 3), hef.symm⟩⟩
      have hfbad : f ∈ bad :=
        Finset.mem_image.mpr ⟨(f, e), hpair, rfl⟩
      exact False.elim ((Finset.mem_sdiff.mp hfF).2 hfbad)
  · have hbadT : bad ⊆ T := by
      intro x hx
      obtain ⟨p, hpC, rfl⟩ := Finset.mem_image.mp hx
      have hpC' : p ∈ (T ×ˢ E).filter (fun p =>
          p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2) := by
        simpa only [C] using hpC
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpC').1).1
    have hcard : F.card + bad.card = T.card := by
      simpa only [F] using Finset.card_sdiff_add_card_eq_card hbadT
    have hbadC : bad.card ≤ C.card := Finset.card_image_le
    have hCle : C.card ≤
        ((T ×ˢ E).filter (fun p =>
          p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)).card := by
      change C.card ≤ C.card
      exact le_rfl
    omega
end RetainedDependency4
export RetainedDependency4 (mme_tripartite_target_isolation_pruning)

-- Accepted source by marwahaha; submission 9fa62f51-1c34-4a0e-a502-0963f6e1e7a3.
namespace RetainedDependency5
open BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem mme_type2_induced_family_of_hash_collision_budget
    {State : Type} {Edge : Type*} {Vertex : Fin 3 → Type*}
    [Fintype State] [Nonempty State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target : State → Finset Edge)
    (htarget : ∀ ω, target ω ⊆ ambient ω)
    (hclosure : ∀ ω, ∀ x ∈ target ω, ∀ y ∈ target ω,
      ∀ z ∈ target ω, supportedMix x y z →
        ∃ e ∈ ambient ω,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (loss : ℝ)
    (hbudget :
      (Fintype.card State : ℝ) * loss +
          ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        ∑ ω, ((target ω).card : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ target ω ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      loss ≤ (kept.card : ℝ) := by
  classical
  let collisions : State → Finset (Edge × Edge) := fun ω ↦
    ((target ω) ×ˢ (ambient ω)).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
  let good : State → ℕ := fun ω ↦ (target ω).card
  let bad : State → ℕ := fun ω ↦ (collisions ω).card
  have hbudget' :
      (Fintype.card State : ℝ) * loss + ∑ ω, (bad ω : ℝ) ≤
        ∑ ω, (good ω : ℝ) := by
    simpa only [bad, good, collisions] using hbudget
  obtain ⟨ω, hω⟩ :=
    mme_finite_collision_budget_averaging_real good bad loss hbudget'
  obtain ⟨kept, hkept, hseparated, hisolated, hcard⟩ :=
    mme_tripartite_target_isolation_pruning
      vertex (ambient ω) (target ω) (htarget ω)
  have hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1) := by
    intro i x y hxy
    apply Subtype.ext
    by_contra hne
    exact hseparated x.1 x.2 y.1 y.2 hne i hxy
  have hinduced : ∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z := by
    intro x y z hsupp
    obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
      hclosure ω x.1 (hkept x.2) y.1 (hkept y.2) z.1 (hkept z.2) hsupp
    have heKept : e ∈ kept := hisolated e heAmbient (by
      intro i
      fin_cases i
      · exact ⟨x.1, x.2, he0⟩
      · exact ⟨y.1, y.2, he1⟩
      · exact ⟨z.1, z.2, he2⟩)
    let e' : kept := ⟨e, heKept⟩
    have hex : e' = x := hmode 0 he0
    have hey : e' = y := hmode 1 he1
    have hez : e' = z := hmode 2 he2
    exact ⟨hex.symm.trans hey, hey.symm.trans hez⟩
  refine ⟨ω, kept, hkept, hmode, hinduced, ?_⟩
  have hcardReal : ((target ω).card : ℝ) ≤
      (kept.card : ℝ) + (collisions ω).card := by
    exact_mod_cast hcard
  have hω' : ((collisions ω).card : ℝ) + loss ≤
      ((target ω).card : ℝ) := by
    simpa only [bad, good] using hω
  linarith
end RetainedDependency5
export RetainedDependency5 (mme_type2_induced_family_of_hash_collision_budget)

-- Accepted source by marwahaha; submission aefa4351-def5-4a5f-8b12-cf301cc7579f.
namespace RetainedDependency6
open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- Uniform one-edge and collision-pair hash fibers, together with a mode
degree bound and the exact target factorization, produce an induced family
with the sharp retained cardinality `V * loss`. -/
theorem mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
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
end RetainedDependency6
export RetainedDependency6 (mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers)

theorem solution
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q : ℕ) (rho loss : ℝ)
    (hstate : Fintype.card State = P * Q)
    (hambientRatio :
      (ambientAll.card : ℝ) ≤ rho * (targetAll.card : ℝ))
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
      (P : ℝ) * loss +
          3 * rho * (targetAll.card : ℝ) ≤ (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      (targetAll.card : ℝ) * loss ≤ (kept.card : ℝ) := by
  have hmargin' : (P : ℝ) * loss + 3 * (ambientAll.card : ℝ) ≤ B := by
    nlinarith [hambientRatio]
  simpa only [Nat.cast_one, mul_one, one_mul] using
    (mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      vertex supportedMix ambientAll targetAll retain
      P B Q ambientAll.card 1 (targetAll.card : ℝ) loss
      (by positivity) hstate (by simp)
      (fun _ _ _ ↦ Finset.card_filter_le _ _)
      hedge hpair htargetAmbient hclosure
      (by simpa using hmargin'))


end AmbientRatioProof

theorem solution
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q : ℕ) (rho loss : ℝ)
    (hstate : Fintype.card State = P * Q)
    (hambientRatio :
      (ambientAll.card : ℝ) ≤ rho * (targetAll.card : ℝ))
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
      (P : ℝ) * loss +
          3 * rho * (targetAll.card : ℝ) ≤ (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      (targetAll.card : ℝ) * loss ≤ (kept.card : ℝ) := by
  exact AmbientRatioProof.solution vertex supportedMix ambientAll targetAll retain
    P B Q rho loss hstate hambientRatio hedge hpair htargetAmbient hclosure hmargin
