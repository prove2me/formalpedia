-- Prove2me | solution 1 for mme_CW_q6_exact_address_joint_xy_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:33:41.244543+00:00
-- url     : https://prove2.me/submissions/053abef3-485a-400c-a357-12e35e78d6ee

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem solution
    {N L G : ℕ} (hLG : L + G = N)
    (address : CWQ6ExactCoupledAddress N L G) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 0 ∧ address.1 1 j = 0)).card = L ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 1 ∧ address.1 1 j = 1)).card = L ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 0 ∧ address.1 1 j = 1)).card = G ∧
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => address.1 0 j = 1 ∧ address.1 1 j = 0)).card = G := by
  have hsupp := address.2.1
  have hmarg := address.2.2
  let C00 : Finset (Fin (2 * N)) :=
    Finset.univ.filter
      (fun j => address.1 0 j = 0 ∧ address.1 1 j = 0)
  let C11 : Finset (Fin (2 * N)) :=
    Finset.univ.filter
      (fun j => address.1 0 j = 1 ∧ address.1 1 j = 1)
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
  have hC00 : C00 = Z0 := by
    ext j
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp [C00, Z0, h0, h1, h2]
  have hC11 : C11 = Z1 := by
    ext j
    rcases hsupp j with h | h | h | h
    all_goals rcases h with ⟨h0, h1, h2⟩
    all_goals simp [C11, Z1, h0, h1, h2]
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
  have hX0 : X0.card = N := by
    simpa [X0, cwQ6CoupledMarginalMultiplicity] using hmarg 0 0
  have hX1 : X1.card = N := by
    simpa [X1, cwQ6CoupledMarginalMultiplicity] using hmarg 0 1
  have hZ0 : Z0.card = L := by
    simpa [Z0, cwQ6CoupledMarginalMultiplicity] using hmarg 2 0
  have hZ1 : Z1.card = L := by
    simpa [Z1, cwQ6CoupledMarginalMultiplicity] using hmarg 2 1
  have h01split := Finset.card_sdiff_add_card_eq_card hZ0sub
  have h10split := Finset.card_sdiff_add_card_eq_card hZ1sub
  change C00.card = L ∧ C11.card = L ∧ C01.card = G ∧ C10.card = G
  rw [hC00, hC11, hC01, hC10]
  omega
