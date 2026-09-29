-- Prove2me | solution 1 for mme_CW_q6_exact_address_profile_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:49:11.155451+00:00
-- url     : https://prove2.me/submissions/f66b37f4-ea2e-4047-af71-e4034e90ccef

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem solution
    {N L G : ℕ} (address : CWQ6ExactCoupledAddress N L G) :
    L + G = N := by
  have hsupp := address.2.1
  have hmarg := address.2.2
  let C01 : Finset (Fin (2 * N)) :=
    Finset.univ.filter
      (fun j => address.1 0 j = 0 ∧ address.1 1 j = 1)
  let C10 : Finset (Fin (2 * N)) :=
    Finset.univ.filter
      (fun j => address.1 0 j = 1 ∧ address.1 1 j = 0)
  let X0 : Finset (Fin (2 * N)) :=
    Finset.univ.filter (fun j => address.1 0 j = 0)
  let X1 : Finset (Fin (2 * N)) :=
    Finset.univ.filter (fun j => address.1 0 j = 1)
  let Z0 : Finset (Fin (2 * N)) :=
    Finset.univ.filter (fun j => address.1 2 j = 0)
  let Z1 : Finset (Fin (2 * N)) :=
    Finset.univ.filter (fun j => address.1 2 j = 1)
  let Z2 : Finset (Fin (2 * N)) :=
    Finset.univ.filter (fun j => address.1 2 j = 2)
  have hZ0sub : Z0 ⊆ X0 := by
    intro j hj
    have hjz := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp_all
  have hZ1sub : Z1 ⊆ X1 := by
    intro j hj
    have hjz := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp_all
  have hC01 : C01 = X0 \ Z0 := by
    ext j
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp [C01, X0, Z0, h0, h1, h2]
  have hC10 : C10 = X1 \ Z1 := by
    ext j
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp [C10, X1, Z1, h0, h1, h2]
  have hZ2 : Z2 = C01 ∪ C10 := by
    ext j
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp [Z2, C01, C10, h0, h1, h2]
  have hdisj : Disjoint C01 C10 := by
    apply Finset.disjoint_left.mpr
    intro j hj01 hj10
    have h01 := (Finset.mem_filter.mp hj01).2
    have h10 := (Finset.mem_filter.mp hj10).2
    simp_all
  have hX0 : X0.card = N := by
    simpa [X0, cwQ6CoupledMarginalMultiplicity] using hmarg 0 0
  have hX1 : X1.card = N := by
    simpa [X1, cwQ6CoupledMarginalMultiplicity] using hmarg 0 1
  have hZ0card : Z0.card = L := by
    simpa [Z0, cwQ6CoupledMarginalMultiplicity] using hmarg 2 0
  have hZ1card : Z1.card = L := by
    simpa [Z1, cwQ6CoupledMarginalMultiplicity] using hmarg 2 1
  have hZ2card : Z2.card = 2 * G := by
    simpa [Z2, cwQ6CoupledMarginalMultiplicity] using hmarg 2 2
  have h01split := Finset.card_sdiff_add_card_eq_card hZ0sub
  have h10split := Finset.card_sdiff_add_card_eq_card hZ1sub
  have hunion := Finset.card_union_of_disjoint hdisj
  rw [← hC01] at h01split
  rw [← hC10] at h10split
  rw [hZ2, hunion] at hZ2card
  omega
