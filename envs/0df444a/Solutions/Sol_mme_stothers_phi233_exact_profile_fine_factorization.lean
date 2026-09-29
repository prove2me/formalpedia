-- Prove2me | solution 1 for mme_stothers_phi233_exact_profile_fine_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:53:48.393871+00:00
-- url     : https://prove2.me/submissions/b2f5194c-7fdb-4a71-b6ed-51ef7f3bc74c

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_exact_label
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_fine_component_restrictions
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option warningAsError true

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

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 10 (fun r ↦
        (MME.StothersFourth.Phi233.componentObj K q r).kronPow
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j))) := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    mme_stothers_phi233_fine_component_restrictions (K := K) q
  have hcomponent : ∀ r : Fin 10,
      TensorObj.Restrict
        (MME.StothersFourth.Phi233.componentObj K q r)
        (MME.StothersFourth.Phi233.fineSourceObj K q r) := by
    intro r
    fin_cases r
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h0
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h1
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h2
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h3
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h4
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h5
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h6
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h7
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h8
    · simpa [MME.StothersFourth.Phi233.componentObj,
        MME.StothersFourth.Phi233.fineSourceObj] using h9
  have hword : TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.componentObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j))) := by
    exact kronFin_restrict (d := 3) (by omega) (2 * N) _ _
      (fun j ↦ hcomponent
        (MME.StothersFourth.Phi233.exactLabelAt address j))
  have hcard : ∀ r : Fin 10,
      Fintype.card
          {j : Fin (2 * N) //
            MME.StothersFourth.Phi233.exactLabelAt address j = r} =
        MME.StothersFourth.Phi233.profileMultiplicity
          alpha beta gamma delta r := by
    intro r
    rw [Fintype.card_subtype]
    rw [← address.2 r]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      rw [MME.StothersFourth.Phi233.addressType_exactLabelAt, hj]
    · intro hj
      apply mme_stothers_phi233_pattern_injective
      rw [← MME.StothersFourth.Phi233.addressType_exactLabelAt address j,
        hj]
  have hgroup := mme_kronFin_group_by_exact_fibers_iso
    (MME.StothersFourth.Phi233.componentObj K q)
    (MME.StothersFourth.Phi233.exactLabelAt address)
    (MME.StothersFourth.Phi233.profileMultiplicity
      alpha beta gamma delta) hcard
  exact TensorObj.Restrict.trans hgroup.2 hword
