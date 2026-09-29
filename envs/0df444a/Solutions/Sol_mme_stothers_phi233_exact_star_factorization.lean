-- Prove2me | solution 1 for mme_stothers_phi233_exact_star_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:52:39.440147+00:00
-- url     : https://prove2.me/submissions/b049c7f7-635c-4542-8ecd-ee1721c9b03a

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_profile_total_and_marginals
import Theorems.Thm_mme_stothers_phi233_exact_profile_card
import Theorems.Thm_mme_stothers_phi233_fixed_mode_profile_table_fiber_card

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option warningAsError true

/-- The exact-profile target family is regular over every realized mode word,
with the same multinomial word factor as the ambient same-marginal family. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 i = a.1.1 i} := by
  classical
  let Marginal := MME.StothersFourth.Phi233.MarginalAddress
    N alpha beta gamma delta
  let Exact := MME.StothersFourth.Phi233.ExactProfileAddress
    N alpha beta gamma delta
  let k : Fin 10 → ℕ :=
    MME.StothersFourth.Phi233.profileMultiplicity alpha beta gamma delta
  let numerator : ℕ :=
    ∏ s : Fin 5,
      (MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta i s).factorial
  let denominator : ℕ := ∏ r : Fin 10, (k r).factorial
  let wordCount : ℕ := (2 * N).factorial / numerator
  have hprofile := mme_stothers_phi233_profile_total_and_marginals
    N alpha beta gamma delta hsum
  have hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s := by
    intro l s
    calc
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
          ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
              (fun r ↦ MME.StothersFourth.Phi233.pattern r l = s),
            k r := by
        symm
        exact Finset.sum_subtype
          ((Finset.univ : Finset (Fin 10)).filter
            (fun r ↦ MME.StothersFourth.Phi233.pattern r l = s))
          (by intro r; simp) k
      _ = ∑ r : Fin 10,
          if MME.StothersFourth.Phi233.pattern r l = s then k r else 0 := by
        exact Finset.sum_filter
          (fun r : Fin 10 ↦ MME.StothersFourth.Phi233.pattern r l = s) k
      _ = MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s := by
        simpa only [k] using hprofile.2 l s
  have hmarginalTotal :
      (∑ s : Fin 5,
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i s) = 2 * N := by
    calc
      (∑ s : Fin 5,
          MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s) =
          ∑ s : Fin 5,
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ a.1.1 i j = s)).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (a.1.2.2 i s).symm
      _ = 2 * N := by
        have h := Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin (2 * N)))
          (Finset.univ : Finset (Fin 5)) (a.1.1 i)
        simpa using h
  have hnumDivFact : numerator ∣ (2 * N).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 5))
      (fun s ↦ MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta i s)
    simpa only [numerator, hmarginalTotal] using h
  have hnumPos : 0 < numerator := by
    exact Finset.prod_pos fun s hs ↦ Nat.factorial_pos _
  have hrowDiv (s : Fin 5) :
      (∏ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r i = s},
          (k r.1).factorial) ∣
        (MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i s).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r i = s})
      (fun r ↦ k r.1)
    simpa [hkMarginal i s] using h
  have hdenPartition :
      (∏ s : Fin 5,
        ∏ r : {r : Fin 10 //
            MME.StothersFourth.Phi233.pattern r i = s},
          (k r.1).factorial) = denominator := by
    calc
      (∏ s : Fin 5,
          ∏ r : {r : Fin 10 //
              MME.StothersFourth.Phi233.pattern r i = s},
            (k r.1).factorial) =
          ∏ x : Sigma fun s : Fin 5 ↦
            {r : Fin 10 //
              MME.StothersFourth.Phi233.pattern r i = s},
            (k x.2.1).factorial := by
        exact (Fintype.prod_sigma
          (fun x : Sigma fun s : Fin 5 ↦
            {r : Fin 10 //
              MME.StothersFourth.Phi233.pattern r i = s} ↦
            (k x.2.1).factorial)).symm
      _ = ∏ r : Fin 10, (k r).factorial := by
        exact
          (Equiv.prod_comp
            (Equiv.sigmaFiberEquiv
              (fun r : Fin 10 ↦
                MME.StothersFourth.Phi233.pattern r i))
            (fun r : Fin 10 ↦ (k r).factorial))
      _ = denominator := rfl
  have hdenDivNum : denominator ∣ numerator := by
    rw [← hdenPartition]
    exact Finset.prod_dvd_prod_of_dvd _ _ (by
      intro s hs
      exact hrowDiv s)
  have hpattern : Function.Injective MME.StothersFourth.Phi233.pattern :=
    mme_stothers_phi233_pattern_injective
  have htableExact (c : Marginal) (r : Fin 10) :
      MME.StothersFourth.Phi233.marginalProfileTable c r =
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ MME.StothersFourth.Phi233.addressType c.1 j =
            MME.StothersFourth.Phi233.pattern r)).card := by
    rw [MME.StothersFourth.Phi233.marginalProfileTable,
      Fintype.card_subtype]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      rw [MME.StothersFourth.Phi233.addressType_marginalLabelAt, hj]
    · intro hj
      apply hpattern
      exact (MME.StothersFourth.Phi233.addressType_marginalLabelAt c j).symm.trans hj
  let ExactStar := {b : Exact // b.1.1 i = a.1.1 i}
  let TableStar := {c : Marginal // c.1 i = a.1.1 i ∧
    MME.StothersFourth.Phi233.marginalProfileTable c = k}
  let eStar : ExactStar ≃ TableStar := {
    toFun b := ⟨b.1.1, b.2, funext fun r ↦
      (htableExact b.1.1 r).trans (b.1.2 r)⟩
    invFun c := ⟨⟨c.1, fun r ↦
      (htableExact c.1 r).symm.trans (congrFun c.2.2 r)⟩, c.2.1⟩
    left_inv b := by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv c := by apply Subtype.ext; rfl
  }
  have hstar : Nat.card ExactStar = numerator / denominator := by
    calc
      Nat.card ExactStar = Nat.card TableStar := Nat.card_congr eStar
      _ = numerator / ∏ r : Fin 10, (k r).factorial := by
        simpa only [TableStar, Marginal, numerator] using
          (mme_stothers_phi233_fixed_mode_profile_table_fiber_card
            N alpha beta gamma delta a.1 i k hkMarginal)
      _ = numerator / denominator := rfl
  have htotal : Nat.card Exact = (2 * N).factorial / denominator := by
    simpa only [Exact, denominator, k] using
      (mme_stothers_phi233_exact_profile_card
        N alpha beta gamma delta hsum)
  have hfactor : (2 * N).factorial / denominator =
      wordCount * (numerator / denominator) := by
    symm
    calc
      wordCount * (numerator / denominator) =
          ((2 * N).factorial / numerator) *
            (numerator / denominator) := by rfl
      _ = (2 * N).factorial * numerator /
          (numerator * denominator) :=
        Nat.div_mul_div_comm hnumDivFact hdenDivNum
      _ = numerator * (2 * N).factorial /
          (numerator * denominator) := by
        rw [Nat.mul_comm (2 * N).factorial numerator]
      _ = (2 * N).factorial / denominator :=
        Nat.mul_div_mul_left (2 * N).factorial denominator hnumPos
  simpa only [Exact, ExactStar, numerator, wordCount, htotal, hstar] using
    hfactor
