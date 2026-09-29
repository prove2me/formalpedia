-- Prove2me | solution 1 for mme_stothers_phi116_exact_address_component_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:12:39.251727+00:00
-- url     : https://prove2.me/submissions/3c240948-012e-4c11-a9ea-5372e3cf2ac8

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data

open MME
open MME.StothersFourth.Phi116

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N alpha beta : ℕ} (hsum : alpha + beta = N)
    (address : CWQ6ExactCoupledAddress N alpha beta) :
    ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ phi116OuterComponent address.1 j = u)).card =
        phi116ComponentMultiplicity alpha beta u := by
  intro u
  have hsupp := address.2.1
  have hmarg := address.2.2
  fin_cases u
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ phi116OuterComponent address.1 j = 0)) =
        Finset.univ.filter (fun j ↦ address.1 2 j = 0) := by
      ext j
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [phi116OuterComponent, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ phi116OuterComponent address.1 j = 0)).card =
        phi116ComponentMultiplicity alpha beta 0
    rw [hset, hmarg 2 0]
    simp [cwQ6CoupledMarginalMultiplicity, phi116ComponentMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ phi116OuterComponent address.1 j = 1)) =
        Finset.univ.filter (fun j ↦ address.1 2 j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [phi116OuterComponent, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ phi116OuterComponent address.1 j = 1)).card =
        phi116ComponentMultiplicity alpha beta 1
    rw [hset, hmarg 2 1]
    simp [cwQ6CoupledMarginalMultiplicity, phi116ComponentMultiplicity]
  · let X0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j ↦ address.1 0 j = 0)
    let Z0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j ↦ address.1 2 j = 0)
    have hsub : Z0 ⊆ X0 := by
      intro j hj
      have hjz := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp_all
    have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ phi116OuterComponent address.1 j = 2)) = X0 \ Z0 := by
      ext j
      simp only [X0, Z0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [phi116OuterComponent, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 0
    have hz := hmarg 2 0
    change X0.card = N at hx
    change Z0.card = alpha at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ phi116OuterComponent address.1 j = 2)).card =
        phi116ComponentMultiplicity alpha beta 2
    rw [hset]
    simp [phi116ComponentMultiplicity]
    omega
  · let X1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j ↦ address.1 0 j = 1)
    let Z1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j ↦ address.1 2 j = 1)
    have hsub : Z1 ⊆ X1 := by
      intro j hj
      have hjz := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp_all
    have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ phi116OuterComponent address.1 j = 3)) = X1 \ Z1 := by
      ext j
      simp only [X1, Z1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [phi116OuterComponent, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 1
    have hz := hmarg 2 1
    change X1.card = N at hx
    change Z1.card = alpha at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ phi116OuterComponent address.1 j = 3)).card =
        phi116ComponentMultiplicity alpha beta 3
    rw [hset]
    simp [phi116ComponentMultiplicity]
    omega
