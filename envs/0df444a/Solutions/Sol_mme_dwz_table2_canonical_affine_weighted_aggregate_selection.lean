-- Prove2me | solution 1 for mme_dwz_table2_canonical_affine_weighted_aggregate_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:40:12.590225+00:00
-- url     : https://prove2.me/submissions/9386a20b-a749-4141-afd2-b0888f300a5d

import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_incidence_factory
import Theorems.Thm_mme_dwz_asymmetric_hash_exact_incidence_sums
import Theorems.Thm_mme_dwz_target_two_mode_collision_card_le_of_degree
import Theorems.Thm_mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
import Theorems.Thm_mme_finset_weighted_collision_averaging_isolated

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

theorem solution
    {p N : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d cap : ℕ) (hcap : 0 < cap) (hmod : 8 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeX (b t)) =
          (fun t ↦ DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeY (b t)) =
          (fun t ↦ DWZSquare.shapeY (a t)))).card ≤ d)
    (mass : ((Fin (N + 2) → ZMod p) × ZMod p) →
      (Fin (N + 1) → Fin 15) → ℕ)
    (hmassCap : ∀ q a, a ∈ T →
      a ∈ dwzTable2AffineHashBucket S A q → mass q a ≤ cap)
    (hmassTotal :
      (7 / 8 : ℝ) *
          ((cap : ℝ) * (T.card : ℝ) * (S.card : ℝ) *
            (p : ℝ) ^ (N + 1)) ≤
        ∑ q : (Fin (N + 2) → ZMod p) × ZMod p,
          (((∑ a ∈ T.filter (fun a ↦
            a ∈ dwzTable2AffineHashBucket S A q), mass q a) : ℕ) : ℝ)) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
      ∃ I : Finset (Fin (N + 1) → Fin 15),
        I ⊆ T ∧
        I ⊆ dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I, ∀ e' ∈ dwzTable2AffineHashBucket S A q,
          (fun t ↦ DWZSquare.shapeX (e t)) =
              (fun t ↦ DWZSquare.shapeX (e' t)) ∨
            (fun t ↦ DWZSquare.shapeY (e t)) =
              (fun t ↦ DWZSquare.shapeY (e' t)) → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by
  classical
  let Edge := Fin (N + 1) → Fin 15
  let XWord := Fin (N + 1) → Fin 5
  let State := (Fin (N + 2) → ZMod p) × ZMod p
  let x : Edge → XWord := fun w t ↦ DWZSquare.shapeX (w t)
  let y : Edge → XWord := fun w t ↦ DWZSquare.shapeY (w t)
  let E : State → Finset Edge := fun q ↦
    dwzTable2AffineHashBucket S A q
  let localColl : State → Finset (Edge × Edge) := fun q ↦
    (((T.filter (fun a ↦ a ∈ E q)).product (E q)).filter
      (fun pair ↦ pair.1 ≠ pair.2 ∧
        (x pair.1 = x pair.2 ∨ y pair.1 = y pair.2)))
  let C : Finset (Edge × Edge) :=
    (T.product A).filter (fun pair ↦ pair.1 ≠ pair.2 ∧
      (x pair.1 = x pair.2 ∨ y pair.1 = y pair.2))
  let lower : ℝ :=
    ((cap : ℝ) * (T.card : ℝ) * (S.card : ℝ)) /
      (2 * (p : ℝ) ^ 2)
  obtain ⟨hstateCard, hE, hsingle, hpair⟩ :=
    mme_dwz_table2_affine_hash_bucket_incidence_factory
      hpodd hp5 S hSrange hSfree A T hTA
  have hincidence := mme_dwz_asymmetric_hash_exact_incidence_sums
    A T x y E N p S.card hE hsingle hpair
  have hcollisions :
      (∑ q : State, (localColl q).card) ≤ C.card * S.card * p ^ N := by
    simpa only [State, Edge, XWord, E, x, y, localColl, C] using
      hincidence.2
  have hC : C.card ≤ 2 * T.card * d := by
    exact mme_dwz_target_two_mode_collision_card_le_of_degree
      A T x y d
        (by simpa only [x, Edge, XWord] using hx)
        (by simpa only [y, Edge, XWord] using hy)
  have hcollisionNat :
      (∑ q : State, cap * (localColl q).card) ≤
        cap * (2 * T.card * d) * S.card * p ^ N := by
    calc
      (∑ q : State, cap * (localColl q).card) =
          cap * ∑ q : State, (localColl q).card := by
            rw [Finset.mul_sum]
      _ ≤ cap * (C.card * S.card * p ^ N) :=
        Nat.mul_le_mul_left cap hcollisions
      _ ≤ cap * ((2 * T.card * d) * S.card * p ^ N) := by
        gcongr
      _ = cap * (2 * T.card * d) * S.card * p ^ N := by ring
  have hcollisionReal :
      (∑ q : State, ((cap * (localColl q).card : ℕ) : ℝ)) ≤
        (cap : ℝ) * (2 * (T.card : ℝ) * (d : ℝ)) *
          (S.card : ℝ) * (p : ℝ) ^ N := by
    exact_mod_cast hcollisionNat
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hnumeric :=
    mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
      N p T.card S.card d cap hp hmod
      (∑ q : State,
        (((∑ a ∈ T.filter (fun a ↦ a ∈ E q), mass q a) : ℕ) : ℝ))
      (∑ q : State, ((cap * (localColl q).card : ℕ) : ℝ))
      (by simpa only [State, Edge, E] using hmassTotal)
      hcollisionReal
  have hbudget :
      (Fintype.card State : ℝ) * lower +
          ∑ q : State, ((cap * (localColl q).card : ℕ) : ℝ) ≤
        ∑ q : State,
          (((∑ a ∈ T.filter (fun a ↦ a ∈ E q), mass q a) : ℕ) : ℝ) := by
    have hstateCardR : (Fintype.card State : ℝ) =
        (p : ℝ) ^ (N + 3) := by
      exact_mod_cast hstateCard
    rw [hstateCardR]
    simpa only [lower] using hnumeric
  obtain ⟨q, I, hIT, hIE, hisolated, hraw⟩ :=
    mme_finset_weighted_collision_averaging_isolated
      T E x y mass cap lower
      (by
        intro q a haT haE
        exact hmassCap q a haT haE)
      (by simpa only [localColl] using hbudget)
  refine ⟨q, I, hIT, hIE, hisolated, ?_⟩
  have hcapR : (0 : ℝ) < (cap : ℝ) := by exact_mod_cast hcap
  norm_num only [Nat.cast_sum] at hraw
  have hdiv := (div_le_div_iff_of_pos_right hcapR).2 hraw
  have hleft : lower / (cap : ℝ) =
      ((T.card : ℝ) * (S.card : ℝ)) /
        (2 * (p : ℝ) ^ 2) := by
    dsimp only [lower]
    field_simp
  have hright :
      (∑ a ∈ I, (mass q a : ℝ)) / (cap : ℝ) =
        ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by
    rw [Finset.sum_div]
  rw [hleft, hright] at hdiv
  exact hdiv
