-- Prove2me | solution 1 for mme_stothers_phi116_exact_address_component_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:13:44.777826+00:00
-- url     : https://prove2.me/submissions/076cb632-5223-4630-9113-e7e8be4bdd02

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Theorems.Thm_mme_stothers_phi116_exact_address_component_counts
import Theorems.Thm_mme_stothers_phi116_outer_component_restrictions

open MME

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem phi116_address_eq_component_address
    {N alpha beta : ℕ}
    (address : CWQ6ExactCoupledAddress N alpha beta)
    (j : Fin (2 * N)) :
    (fun s ↦ address.1 s j) =
      phi116ComponentAddress (phi116OuterComponent address.1 j) := by
  rcases address.2.1 j with h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2⟩
  all_goals funext s
  all_goals fin_cases s
  all_goals simp [phi116ComponentAddress, phi116OuterComponent, h0, h1, h2]

private theorem phi116ComponentObj_restrict_outer_block
    {K : Type u} [Field K] (r : Fin 4) :
    TensorObj.Restrict (phi116ComponentObj K r)
      ((cwPhi116ThreeGrading K).blockSubtensor
        (phi116ComponentAddress r)) := by
  obtain ⟨h012, h102, h000, h111⟩ :=
    mme_stothers_phi116_outer_component_restrictions (K := K)
  fin_cases r
  · simpa [phi116ComponentObj, phi116ComponentAddress] using h000
  · simpa [phi116ComponentObj, phi116ComponentAddress] using h111
  · simpa [phi116ComponentObj, phi116ComponentAddress] using h012
  · simpa [phi116ComponentObj, phi116ComponentAddress] using h102

private theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft : P.le
      (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright : P.le
      (TensorQ.toQ X' * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem kronFin_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ r, TensorObj.Restrict (X r) (Y r)) →
      TensorObj.Restrict (TensorObj.kronFin n X)
        (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y _
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun r ↦ X r.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun r ↦ Y r.succ)))
      exact kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

end MME.StothersFourth.Phi116

open MME.StothersFourth.Phi116

theorem solution
    {K : Type u} [Field K] {N alpha beta : ℕ}
    (hsum : alpha + beta = N)
    (address : CWQ6ExactCoupledAddress N alpha beta) :
    TensorObj.Restrict
      (TensorObj.kronFin 4 (fun r ↦
        (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
          (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
            alpha beta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K) address.1) := by
  classical
  let word : Fin (2 * N) → Fin 4 :=
    fun j ↦ phi116OuterComponent address.1 j
  have hEach : ∀ j : Fin (2 * N),
      TensorObj.Restrict (phi116ComponentObj K (word j))
        ((cwPhi116ThreeGrading K).blockSubtensor
          (fun s ↦ address.1 s j)) := by
    intro j
    rw [phi116_address_eq_component_address address j]
    exact phi116ComponentObj_restrict_outer_block (K := K) (word j)
  have hword : TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦ phi116ComponentObj K (word j)))
      (gradedAddressBlock (cwPhi116ThreeGrading K) address.1) := by
    change TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦ phi116ComponentObj K (word j)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        (cwPhi116ThreeGrading K).blockSubtensor
          (fun s ↦ address.1 s j)))
    exact kronFin_restrict (d := 3) (by omega) (2 * N) _ _ hEach
  have hcounts :=
    mme_stothers_phi116_exact_address_component_counts hsum address
  have hcard : ∀ r : Fin 4,
      Fintype.card {j : Fin (2 * N) // word j = r} =
        phi116ComponentMultiplicity alpha beta r := by
    intro r
    let S : Set (Fin (2 * N)) := {j | word j = r}
    change Fintype.card S = phi116ComponentMultiplicity alpha beta r
    calc
      Fintype.card S =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ word j = r)).card :=
        Fintype.card_ofFinset _ (by
          intro j
          simp [S])
      _ = phi116ComponentMultiplicity alpha beta r := by
        simpa only [word] using hcounts r
  have hgroup := mme_kronFin_group_by_exact_fibers_iso
    (phi116ComponentObj K) word
      (phi116ComponentMultiplicity alpha beta) hcard
  exact TensorObj.Restrict.trans hgroup.2 hword
