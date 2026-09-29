-- Prove2me | solution 1 for mme_stothers_phi233_exact_profile_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:00:25.984477+00:00
-- url     : https://prove2.me/submissions/ea1c1a4a-652a-4166-b8f3-11f26ab37eda

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty
import Theorems.Thm_mme_stothers_phi233_pattern_injective

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Nonempty
      (MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) := by
  let multiplicity : Fin 10 → ℕ :=
    MME.StothersFourth.Phi233.profileMultiplicity alpha beta gamma delta
  have htotal : (∑ r : Fin 10, multiplicity r) = 2 * N := by
    simp [multiplicity, MME.StothersFourth.Phi233.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  have hsumUnit : ∀ _i : PUnit.{1},
      (∑ r : {r : Fin 10 // (PUnit.unit : PUnit.{1}) = PUnit.unit},
        multiplicity r.1) =
        Fintype.card
          {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} := by
    intro i
    let eBeta :
        {r : Fin 10 // (PUnit.unit : PUnit.{1}) = PUnit.unit} ≃ Fin 10 :=
      { toFun := Subtype.val
        invFun := fun r ↦ ⟨r, rfl⟩
        left_inv := fun r ↦ Subtype.ext rfl
        right_inv := fun r ↦ rfl }
    let eAlpha :
        {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} ≃
        Fin (2 * N) :=
      { toFun := Subtype.val
        invFun := fun j ↦ ⟨j, rfl⟩
        left_inv := fun j ↦ Subtype.ext rfl
        right_inv := fun j ↦ rfl }
    calc
      (∑ r : {r : Fin 10 // (PUnit.unit : PUnit.{1}) = PUnit.unit},
          multiplicity r.1) =
          ∑ r : Fin 10, multiplicity r :=
        Fintype.sum_equiv eBeta _ _ (fun _ ↦ rfl)
      _ = 2 * N := htotal
      _ = Fintype.card (Fin (2 * N)) := by simp
      _ = Fintype.card
          {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} :=
        (Fintype.card_congr eAlpha).symm
  obtain ⟨g, _hgGrade, hgFiber⟩ :=
    mme_fintype_constrained_prescribed_fiber_function_nonempty
      (alpha := Fin (2 * N)) (beta := Fin 10) (iota := PUnit.{1})
      (fun _ ↦ PUnit.unit) (fun _ ↦ PUnit.unit) multiplicity hsumUnit
  have hpattern : Function.Injective MME.StothersFourth.Phi233.pattern :=
    mme_stothers_phi233_pattern_injective
  let x : MME.StothersFourth.Phi233.ProfileAddress N :=
    fun i j ↦ MME.StothersFourth.Phi233.pattern (g j) i
  have hsupported : MME.StothersFourth.Phi233.CoordinatewiseSupported x := by
    intro j
    exact ⟨g j, rfl⟩
  have hexact : ∀ r : Fin 10,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi233.addressType x j =
          MME.StothersFourth.Phi233.pattern r)).card = multiplicity r := by
    intro r
    have hgfiber :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r)).card = multiplicity r := by
      rw [← Fintype.card_subtype]
      exact hgFiber r
    calc
      ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ MME.StothersFourth.Phi233.addressType x j =
            MME.StothersFourth.Phi233.pattern r)).card =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ g j = r)).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change
          MME.StothersFourth.Phi233.pattern (g j) =
              MME.StothersFourth.Phi233.pattern r ↔
            g j = r
        exact hpattern.eq_iff
      _ = multiplicity r := hgfiber
  have hmarginal : ∀ i : Fin 3, ∀ k : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ x i j = k)).card =
          MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i k := by
    intro i k
    have hgfiber : ∀ r : Fin 10,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r)).card = multiplicity r := by
      intro r
      rw [← Fintype.card_subtype]
      exact hgFiber r
    have hpartition :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ x i j = k)).card =
          ∑ r : Fin 10,
            if MME.StothersFourth.Phi233.pattern r i = k then
              multiplicity r else 0 := by
      calc
        ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ x i j = k)).card =
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ g j ∈
                (Finset.univ : Finset (Fin 10)).filter
                  (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k))).card := by
              congr 1
              ext j
              simp [x]
        _ = ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
              (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k),
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ g j = r)).card := by
              symm
              exact Finset.sum_card_fiberwise_eq_card_filter
                (Finset.univ : Finset (Fin (2 * N)))
                ((Finset.univ : Finset (Fin 10)).filter
                  (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k)) g
        _ = ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
              (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k),
              multiplicity r := by
              apply Finset.sum_congr rfl
              intro r hr
              exact hgfiber r
        _ = ∑ r : Fin 10,
              if MME.StothersFourth.Phi233.pattern r i = k then
                multiplicity r else 0 := by
              exact Finset.sum_filter
                (fun r : Fin 10 ↦
                  MME.StothersFourth.Phi233.pattern r i = k)
                multiplicity
    rw [hpartition]
    fin_cases i <;> fin_cases k <;>
      simp [multiplicity,
        MME.StothersFourth.Phi233.pattern,
        MME.StothersFourth.Phi233.profileMultiplicity,
        MME.StothersFourth.Phi233.marginalMultiplicity,
        MME.cwSquareBlockType, Fin.sum_univ_succ] <;> omega
  let xm : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta := ⟨x, hsupported, hmarginal⟩
  refine ⟨⟨xm, ?_⟩⟩
  intro r
  change
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ MME.StothersFourth.Phi233.addressType x j =
        MME.StothersFourth.Phi233.pattern r)).card = multiplicity r
  exact hexact r
