-- Prove2me | solution 1 for mme_CW_q6_exact_coupled_address_regularity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:35:46.911056+00:00
-- url     : https://prove2.me/submissions/3edc90da-2ae9-492d-a365-d0773024ca97

import Mathlib
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 2000000

private def q6AtomMode (u : Fin 4) : Fin 3 → Fin 3 :=
  if u = 0 then ![0, 0, 0]
  else if u = 1 then ![1, 1, 1]
  else if u = 2 then ![0, 1, 2]
  else ![1, 0, 2]

private def q6Decode {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    CWQ6CoupledAddress N :=
  fun i j => q6AtomMode (t j) i

private def q6Encode {N : ℕ} (a : CWQ6CoupledAddress N) :
    Fin (2 * N) → Fin 4 := fun j =>
  if a 2 j = 0 then 0
  else if a 2 j = 1 then 1
  else if a 0 j = 0 then 2
  else 3

private theorem q6AtomMode_encode
    {N : ℕ} (a : CWQ6CoupledAddress N)
    (ha : CWQ6CoupledCoordinatewiseSupported a) :
    q6Decode (q6Encode a) = a := by
  funext i j
  rcases ha j with h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2⟩
  all_goals fin_cases i <;> simp [q6Decode, q6Encode, q6AtomMode, h0, h1, h2]

private theorem q6Encode_decode
    {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    q6Encode (q6Decode t) = t := by
  funext j
  generalize hu : t j = u
  fin_cases u <;> simp [q6Encode, q6Decode, q6AtomMode, hu]

private theorem q6Decode_supported
    {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    CWQ6CoupledCoordinatewiseSupported (q6Decode t) := by
  intro j
  generalize hu : t j = u
  fin_cases u <;> simp [q6Decode, q6AtomMode, hu]

private def q6AtomMultiplicity (L G : ℕ) (u : Fin 4) : ℕ :=
  if u = 0 then L else if u = 1 then L else G

private theorem card_filter_two_values
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (t : α → β) (r s : β) (hrs : r ≠ s) :
    ((Finset.univ : Finset α).filter (fun j => t j = r ∨ t j = s)).card =
      ((Finset.univ : Finset α).filter (fun j => t j = r)).card +
        ((Finset.univ : Finset α).filter (fun j => t j = s)).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro j hjr hjs
  have hr := (Finset.mem_filter.mp hjr).2
  have hs := (Finset.mem_filter.mp hjs).2
  exact hrs (hr.symm.trans hs)

private theorem q6Encode_profile
    {N L G : ℕ} (hLG : L + G = N)
    (a : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported a)
    (hmarg : ∀ i r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => a i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => q6Encode a j = u)).card = q6AtomMultiplicity L G u := by
  intro u
  fin_cases u
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 0)) =
        Finset.univ.filter (fun j => a 2 j = 0) := by
      ext j
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 0)).card = q6AtomMultiplicity L G 0
    rw [hset, hmarg 2 0]
    simp [cwQ6CoupledMarginalMultiplicity, q6AtomMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 1)) =
        Finset.univ.filter (fun j => a 2 j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 1)).card = q6AtomMultiplicity L G 1
    rw [hset, hmarg 2 1]
    simp [cwQ6CoupledMarginalMultiplicity, q6AtomMultiplicity]
  · let X0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 0 j = 0)
    let Z0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 2 j = 0)
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
          (fun j => q6Encode a j = 2)) = X0 \ Z0 := by
      ext j
      simp only [X0, Z0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, X0, Z0, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 0
    have hz := hmarg 2 0
    change X0.card = N at hx
    change Z0.card = L at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 2)).card = q6AtomMultiplicity L G 2
    rw [hset]
    simp [q6AtomMultiplicity]
    omega
  · let X1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 0 j = 1)
    let Z1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 2 j = 1)
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
          (fun j => q6Encode a j = 3)) = X1 \ Z1 := by
      ext j
      simp only [X1, Z1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, X1, Z1, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 1
    have hz := hmarg 2 1
    change X1.card = N at hx
    change Z1.card = L at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 3)).card = q6AtomMultiplicity L G 3
    rw [hset]
    simp [q6AtomMultiplicity]
    omega

private theorem q6Decode_marginals
    {N L G : ℕ} (hLG : L + G = N)
    (t : Fin (2 * N) → Fin 4)
    (hprof : ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => t j = u)).card = q6AtomMultiplicity L G u) :
    ∀ i r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => q6Decode t i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r := by
  have hpair (u v : Fin 4) (huv : u ≠ v) :
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => t j = u ∨ t j = v)).card =
          q6AtomMultiplicity L G u + q6AtomMultiplicity L G v := by
    rw [card_filter_two_values t u v huv, hprof u, hprof v]
  intro i r
  fin_cases i <;> fin_cases r
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 0)) =
        Finset.univ.filter (fun j => t j = 0 ∨ t j = 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 0
    rw [hset, hpair 0 2 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 1)) =
        Finset.univ.filter (fun j => t j = 1 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 1
    rw [hset, hpair 1 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 2)) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 2
    rw [hset]
    simp [cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 0)) =
        Finset.univ.filter (fun j => t j = 0 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 0
    rw [hset, hpair 0 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 1)) =
        Finset.univ.filter (fun j => t j = 1 ∨ t j = 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 1
    rw [hset, hpair 1 2 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 2)) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 2
    rw [hset]
    simp [cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 0)) =
        Finset.univ.filter (fun j => t j = 0) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 0
    rw [hset, hprof 0]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 1)) =
        Finset.univ.filter (fun j => t j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 1
    rw [hset, hprof 1]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 2)) =
        Finset.univ.filter (fun j => t j = 2 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 2
    rw [hset, hpair 2 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
    omega

private def Q6AtomProfile (N L G : ℕ) : Type :=
  {t : Fin (2 * N) → Fin 4 // ∀ u : Fin 4,
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => t j = u)).card = q6AtomMultiplicity L G u}

private noncomputable instance q6CoupledAddressFintype (N : ℕ) :
    Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

private noncomputable instance q6ExactCoupledAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  by
    classical
    unfold CWQ6ExactCoupledAddress
    infer_instance

private noncomputable instance q6AtomProfileFintype
    (N L G : ℕ) : Fintype (Q6AtomProfile N L G) :=
  by
    classical
    unfold Q6AtomProfile
    infer_instance

private noncomputable def q6ExactAtomEquiv
    {N L G : ℕ} (hLG : L + G = N) :
    CWQ6ExactCoupledAddress N L G ≃ Q6AtomProfile N L G where
  toFun a := ⟨q6Encode a.1, q6Encode_profile hLG a.1 a.2.1 a.2.2⟩
  invFun t := ⟨q6Decode t.1, q6Decode_supported t.1,
    q6Decode_marginals hLG t.1 t.2⟩
  left_inv a := Subtype.ext (q6AtomMode_encode a.1 a.2.1)
  right_inv t := Subtype.ext (q6Encode_decode t.1)

private theorem q6ExactAddresses_card_eq_fintype
    (N L G : ℕ) :
    (cwQ6ExactAddresses N L G).card =
      Fintype.card (CWQ6ExactCoupledAddress N L G) := by
  classical
  change
    ((Finset.univ : Finset (CWQ6CoupledAddress N)).filter (fun a =>
      CWQ6CoupledCoordinatewiseSupported a ∧
        ∀ i r : Fin 3,
          (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
            cwQ6CoupledMarginalMultiplicity N L G i r)).card = _
  symm
  exact Fintype.card_subtype _

private theorem q6AtomProfile_card_multinomial
    {N L G : ℕ} (hLG : L + G = N) :
    Fintype.card (Q6AtomProfile N L G) =
      Nat.multinomial (Finset.univ : Finset (Fin 4))
        (q6AtomMultiplicity L G) := by
  have hsum' : ∑ u : Fin 4, q6AtomMultiplicity L G u = 2 * N := by
    simp [Fin.sum_univ_four, q6AtomMultiplicity]
    omega
  have hsum : ∑ u : Fin 4, q6AtomMultiplicity L G u =
      Fintype.card (Fin (2 * N)) := by simpa using hsum'
  have h := mme_fintype_prescribed_fiber_function_card
    (q6AtomMultiplicity L G) hsum
  have hfiber (t : Fin (2 * N) → Fin 4) (u : Fin 4) :
      Fintype.card {j : Fin (2 * N) // t j = u} =
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => t j = u)).card := by
    exact Fintype.card_subtype _
  simp_rw [hfiber] at h
  rw [Nat.multinomial, hsum']
  change Fintype.card (Q6AtomProfile N L G) = _ at h
  simpa using h

private theorem q6AtomProfile_card
    {N L G : ℕ} (hLG : L + G = N) :
    Fintype.card (Q6AtomProfile N L G) =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G := by
  rw [q6AtomProfile_card_multinomial hLG]
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    decide
  rw [huniv]
  rw [Nat.multinomial_insert (a := (0 : Fin 4)) (s := {1, 2, 3})
    (by decide) (q6AtomMultiplicity L G)]
  rw [Nat.multinomial_insert (a := (1 : Fin 4)) (s := {2, 3})
    (by decide) (q6AtomMultiplicity L G)]
  rw [Nat.binomial_eq_choose (a := (2 : Fin 4)) (b := 3)
    (f := q6AtomMultiplicity L G) (by decide)]
  simp [q6AtomMultiplicity]
  have htwon : L + (L + (G + G)) = 2 * N := by omega
  have hrest : L + (G + G) = 2 * N - L := by omega
  have htwoG : G + G = 2 * G := by omega
  rw [htwon, hrest, htwoG]
  simp [Nat.mul_assoc]

private theorem q6ExactAddresses_card
    {N L G : ℕ} (hLG : L + G = N) :
    (cwQ6ExactAddresses N L G).card =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G := by
  rw [q6ExactAddresses_card_eq_fintype]
  rw [Fintype.card_congr (q6ExactAtomEquiv hLG)]
  exact q6AtomProfile_card hLG

private def q6AtomsAt (i r : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter (fun u => q6AtomMode u i = r)

private def q6AtomFactorialDenominator
    (L G : ℕ) (i r : Fin 3) : ℕ :=
  if i = 2 then
    if r = 0 then L.factorial
    else if r = 1 then L.factorial
    else G.factorial * G.factorial
  else if r = 0 then L.factorial * G.factorial
  else if r = 1 then L.factorial * G.factorial
  else 1

private theorem q6AtomFiberMultiplicity_sum
    (N L G : ℕ) (hLG : L + G = N) (i r : Fin 3) :
    (∑ u : {u : Fin 4 // q6AtomMode u i = r},
      q6AtomMultiplicity L G u.1) =
        cwQ6CoupledMarginalMultiplicity N L G i r := by
  rw [← Finset.sum_subtype (q6AtomsAt i r)
    (by intro u; simp [q6AtomsAt]) (q6AtomMultiplicity L G)]
  fin_cases i <;> fin_cases r <;>
    simp only [q6AtomsAt, Finset.sum_filter, Fin.sum_univ_four] <;>
    simp [q6AtomMode, q6AtomMultiplicity,
      cwQ6CoupledMarginalMultiplicity] <;> omega

private theorem q6AtomFiberFactorial_prod
    (L G : ℕ) (i r : Fin 3) :
    (∏ u : {u : Fin 4 // q6AtomMode u i = r},
      (q6AtomMultiplicity L G u.1).factorial) =
        q6AtomFactorialDenominator L G i r := by
  rw [← Finset.prod_subtype (q6AtomsAt i r)
    (by intro u; simp [q6AtomsAt])
    (fun u => (q6AtomMultiplicity L G u).factorial)]
  fin_cases i <;> fin_cases r <;>
    simp only [q6AtomsAt, Finset.prod_filter, Fin.prod_univ_four] <;>
    simp [q6AtomMode, q6AtomMultiplicity,
      q6AtomFactorialDenominator]

private theorem mem_q6ExactAddresses_iff
    {N L G : ℕ} (a : CWQ6CoupledAddress N) :
    a ∈ cwQ6ExactAddresses N L G ↔
      CWQ6CoupledCoordinatewiseSupported a ∧
        ∀ i r : Fin 3,
          (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
            cwQ6CoupledMarginalMultiplicity N L G i r := by
  classical
  simp [cwQ6ExactAddresses]

private def Q6AtomProfileOver
    (N L G : ℕ) (i : Fin 3) (w : Fin (2 * N) → Fin 3) : Type :=
  {t : Fin (2 * N) → Fin 4 //
    (∀ j, q6AtomMode (t j) i = w j) ∧
      ∀ u : Fin 4,
        Fintype.card {j : Fin (2 * N) // t j = u} =
          q6AtomMultiplicity L G u}

private noncomputable def q6ExactFinsetFiberEquiv
    {N L G : ℕ} (i : Fin 3) (w : Fin (2 * N) → Fin 3) :
    {a : CWQ6CoupledAddress N //
      a ∈ (cwQ6ExactAddresses N L G).filter (fun e => e i = w)} ≃
    {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} where
  toFun a := by
    have ha := Finset.mem_filter.mp a.2
    exact ⟨⟨a.1, (mem_q6ExactAddresses_iff a.1).mp ha.1⟩, ha.2⟩
  invFun a :=
    ⟨a.1.1, Finset.mem_filter.mpr
      ⟨(mem_q6ExactAddresses_iff a.1.1).mpr a.1.2, a.2⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext (Subtype.ext rfl)

private noncomputable def q6ExactFiberAtomEquiv
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3) :
    {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} ≃
      Q6AtomProfileOver N L G i w where
  toFun a := by
    refine ⟨q6Encode a.1.1, ?_, ?_⟩
    · intro j
      have hdec := q6AtomMode_encode a.1.1 a.1.2.1
      have hj := congrFun (congrFun hdec i) j
      have hj' : q6AtomMode (q6Encode a.1.1 j) i = a.1.1 i j := by
        simpa [q6Decode] using hj
      exact hj'.trans (congrFun a.2 j)
    · intro u
      exact (Fintype.card_subtype _).trans
        (q6Encode_profile hLG a.1.1 a.1.2.1 a.1.2.2 u)
  invFun t := by
    have hprof : ∀ u : Fin 4,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => t.1 j = u)).card = q6AtomMultiplicity L G u := by
      intro u
      exact (Fintype.card_subtype _).symm.trans (t.2.2 u)
    refine ⟨⟨q6Decode t.1, q6Decode_supported t.1,
      q6Decode_marginals hLG t.1 hprof⟩, ?_⟩
    funext j
    exact t.2.1 j
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact q6AtomMode_encode a.1.1 a.1.2.1
  right_inv t := Subtype.ext (q6Encode_decode t.1)

private theorem q6AtomProfileOver_card_formula
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    Nat.card (Q6AtomProfileOver N L G i w) =
      ∏ r : Fin 3,
        (cwQ6CoupledMarginalMultiplicity N L G i r).factorial /
          q6AtomFactorialDenominator L G i r := by
  have hsum (r : Fin 3) :
      (∑ u : {u : Fin 4 // q6AtomMode u i = r},
        q6AtomMultiplicity L G u.1) =
          Fintype.card {j : Fin (2 * N) // w j = r} := by
    rw [q6AtomFiberMultiplicity_sum N L G hLG i r]
    exact ((Fintype.card_subtype _).trans (hw r)).symm
  have h := mme_fintype_constrained_prescribed_fiber_function_card
    w (fun u : Fin 4 => q6AtomMode u i) (q6AtomMultiplicity L G) hsum
  change Nat.card (Q6AtomProfileOver N L G i w) = _ at h
  have hwcard (r : Fin 3) :
      Fintype.card {j : Fin (2 * N) // w j = r} =
        cwQ6CoupledMarginalMultiplicity N L G i r :=
    (Fintype.card_subtype _).trans (hw r)
  simp_rw [hwcard, q6AtomFiberFactorial_prod] at h
  exact h

private theorem q6AtomProfileOver_card
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    Nat.card (Q6AtomProfileOver N L G i w) =
      if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
  have h := q6AtomProfileOver_card_formula hLG i w hw
  have hchooseN : Nat.choose N G =
      N.factorial / (L.factorial * G.factorial) := by
    rw [← hLG]
    exact Nat.add_choose L G
  have hchooseG : Nat.choose (2 * G) G =
      (2 * G).factorial / (G.factorial * G.factorial) := by
    rw [show 2 * G = G + G by omega]
    exact Nat.add_choose G G
  have hfacL : L.factorial / L.factorial = 1 :=
    Nat.div_self (Nat.factorial_pos L)
  fin_cases i
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseN, pow_two] using h
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseN, pow_two] using h
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseG,
      hfacL] using h

private theorem q6ExactFiber_card
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    ((cwQ6ExactAddresses N L G).filter (fun e => e i = w)).card =
      if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
  let S : Finset (CWQ6CoupledAddress N) :=
    (cwQ6ExactAddresses N L G).filter
      (fun e : CWQ6CoupledAddress N => e i = w)
  change S.card = _
  calc
    S.card = Fintype.card ↑S := (Fintype.card_coe S).symm
    _ = Nat.card ↑S := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} :=
      Nat.card_congr (by
        simpa only [S] using q6ExactFinsetFiberEquiv (L := L) (G := G) i w)
    _ = Nat.card (Q6AtomProfileOver N L G i w) :=
      Nat.card_congr (q6ExactFiberAtomEquiv hLG i w)
    _ = _ := q6AtomProfileOver_card hLG i w hw

private theorem q6_choose_factorization
    {N L G : ℕ} (hLG : L + G = N) :
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 := by
  have hLle : L ≤ 2 * N := by omega
  have hLrest : L ≤ 2 * N - L := by omega
  have hGle : G ≤ N := by omega
  have hNle : N ≤ 2 * N := by omega
  have hrest : 2 * N - L - L = 2 * G := by omega
  have hNG : N - G = L := by omega
  have hGG : 2 * G - G = G := by omega
  have hNN : 2 * N - N = N := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hLle
  have h2 := Nat.choose_mul_factorial_mul_factorial hLrest
  have h3 := Nat.choose_mul_factorial_mul_factorial (show G ≤ 2 * G by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial hNle
  have h5 := Nat.choose_mul_factorial_mul_factorial hGle
  change Nat.choose (2 * N) L * L.factorial * (2 * N - L).factorial =
    (2 * N).factorial at h1
  change Nat.choose (2 * N - L) L * L.factorial *
    (2 * N - L - L).factorial = (2 * N - L).factorial at h2
  rw [hrest] at h2
  rw [hGG] at h3
  change Nat.choose (2 * G) G * G.factorial * G.factorial =
    (2 * G).factorial at h3
  rw [hNN] at h4
  change Nat.choose (2 * N) N * N.factorial * N.factorial =
    (2 * N).factorial at h4
  change Nat.choose N G * G.factorial * (N - G).factorial =
    N.factorial at h5
  rw [hNG] at h5
  let D := L.factorial * L.factorial * G.factorial * G.factorial
  have hleft :
      ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G) * D = (2 * N).factorial := by
    dsimp [D]
    calc
      _ = Nat.choose (2 * N) L * L.factorial *
          (Nat.choose (2 * N - L) L * L.factorial *
            (Nat.choose (2 * G) G * G.factorial * G.factorial)) := by ring
      _ = Nat.choose (2 * N) L * L.factorial *
          (Nat.choose (2 * N - L) L * L.factorial *
            (2 * G).factorial) := by rw [h3]
      _ = Nat.choose (2 * N) L * L.factorial *
          (2 * N - L).factorial := by rw [h2]
      _ = (2 * N).factorial := h1
  have hright :
      (Nat.choose (2 * N) N * (Nat.choose N G) ^ 2) * D =
        (2 * N).factorial := by
    dsimp [D]
    calc
      _ = Nat.choose (2 * N) N *
          (Nat.choose N G * G.factorial * L.factorial) *
          (Nat.choose N G * G.factorial * L.factorial) := by ring
      _ = Nat.choose (2 * N) N * N.factorial * N.factorial := by
        rw [h5]
      _ = (2 * N).factorial := h4
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < D)
    (hleft.trans hright.symm)

private theorem q6ModeWord_marginals
    {N L G : ℕ} (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : w ∈ (cwQ6ExactAddresses N L G).image (fun e => e i)) :
    ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r := by
  classical
  rcases Finset.mem_image.mp hw with ⟨a, ha, hai⟩
  intro r
  rw [← hai]
  exact ((mem_q6ExactAddresses_iff a).mp ha).2 i r

private theorem q6ModeWords_card
    {N L G : ℕ} (hLG : L + G = N) (i : Fin 3) :
    ((cwQ6ExactAddresses N L G).image (fun e => e i)).card =
      if i = 2 then
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      else Nat.choose (2 * N) N := by
  classical
  let A := cwQ6ExactAddresses N L G
  let W := A.image (fun e => e i)
  have hdegree (w : Fin (2 * N) → Fin 3) (hw : w ∈ W) :
      (A.filter (fun e => e i = w)).card =
        if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
    apply q6ExactFiber_card hLG i w
    exact q6ModeWord_marginals i w (by simpa [A, W] using hw)
  have hsum := Finset.card_eq_sum_card_image (fun e : CWQ6CoupledAddress N => e i) A
  have hconst :
      (∑ w ∈ W, (A.filter (fun e => e i = w)).card) =
        W.card * (if i = 2 then Nat.choose (2 * G) G
          else (Nat.choose N G) ^ 2) :=
    Finset.sum_const_nat hdegree
  change A.card = ∑ w ∈ W, (A.filter (fun e => e i = w)).card at hsum
  rw [hconst] at hsum
  fin_cases i
  · have hpos : 0 < (Nat.choose N G) ^ 2 := by
      have : 0 < Nat.choose N G := Nat.choose_pos (by omega)
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * (Nat.choose N G) ^ 2 = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG
      _ = Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 :=
        q6_choose_factorization hLG
  · have hpos : 0 < (Nat.choose N G) ^ 2 := by
      have : 0 < Nat.choose N G := Nat.choose_pos (by omega)
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * (Nat.choose N G) ^ 2 = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG
      _ = Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 :=
        q6_choose_factorization hLG
  · have hpos : 0 < Nat.choose (2 * G) G :=
      Nat.choose_pos (by omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * Nat.choose (2 * G) G = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG

theorem solution
    (N L G : ℕ) (hLG : L + G = N) :
    CWQ6ExactAddressRegularity N L G := by
  classical
  refine ⟨q6ExactAddresses_card hLG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cwQ6ExactXWords] using
      q6ModeWords_card hLG (0 : Fin 3)
  · simpa [cwQ6ExactYWords] using
      q6ModeWords_card hLG (1 : Fin 3)
  · simpa [cwQ6ExactZWords] using
      q6ModeWords_card hLG (2 : Fin 3)
  · intro x hx
    have hx' : x ∈ (cwQ6ExactAddresses N L G).image (fun e => e 0) := by
      simpa [cwQ6ExactXWords] using hx
    simpa using q6ExactFiber_card hLG (0 : Fin 3) x
      (q6ModeWord_marginals 0 x hx')
  · intro y hy
    have hy' : y ∈ (cwQ6ExactAddresses N L G).image (fun e => e 1) := by
      simpa [cwQ6ExactYWords] using hy
    simpa using q6ExactFiber_card hLG (1 : Fin 3) y
      (q6ModeWord_marginals 1 y hy')
  · intro z hz
    have hz' : z ∈ (cwQ6ExactAddresses N L G).image (fun e => e 2) := by
      simpa [cwQ6ExactZWords] using hz
    simpa using q6ExactFiber_card hLG (2 : Fin 3) z
      (q6ModeWord_marginals 2 z hz')
