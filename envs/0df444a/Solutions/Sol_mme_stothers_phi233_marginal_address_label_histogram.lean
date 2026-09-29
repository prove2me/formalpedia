-- Prove2me | solution 1 for mme_stothers_phi233_marginal_address_label_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:19:40.58558+00:00
-- url     : https://prove2.me/submissions/02166620-f6df-4145-b303-defbfc28298c

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (x : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) :
    ∃ g : Fin (2 * N) → Fin 10,
      (∀ i j,
        x.1 i j = MME.StothersFourth.Phi233.pattern (g j) i) ∧
      let w : Fin 10 → ℕ := fun r ↦
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r)).card
      (∑ r : Fin 10, w r) = 2 * N ∧
      w 0 + w 1 + w 2 = 2 * alpha + beta ∧
      w 7 + w 8 + w 9 = 2 * alpha + beta ∧
      w 3 + w 7 = alpha + gamma ∧
      w 2 + w 6 = alpha + gamma ∧
      w 6 + w 9 = alpha + gamma ∧
      w 0 + w 3 = alpha + gamma := by
  classical
  let g : Fin (2 * N) → Fin 10 := fun j ↦
    Classical.choose (x.2.1 j)
  have hcoord : ∀ i j,
      x.1 i j = MME.StothersFourth.Phi233.pattern (g j) i := by
    intro i j
    exact congrFun (Classical.choose_spec (x.2.1 j)) i
  let w : Fin 10 → ℕ := fun r ↦
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ g j = r)).card
  have htotal : (∑ r : Fin 10, w r) = 2 * N := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (2 * N)))
      (Finset.univ : Finset (Fin 10)) g
    simpa [w] using h
  have hpartition : ∀ i : Fin 3, ∀ k : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ x.1 i j = k)).card =
        ∑ r : Fin 10,
          if MME.StothersFourth.Phi233.pattern r i = k then w r else 0 := by
    intro i k
    calc
      ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ x.1 i j = k)).card =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦
              MME.StothersFourth.Phi233.pattern (g j) i = k)).card := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hcoord i j]
      _ = ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ g j ∈
              (Finset.univ : Finset (Fin 10)).filter
                (fun r ↦
                  MME.StothersFourth.Phi233.pattern r i = k))).card := by
            congr 1
            ext j
            simp
      _ = ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
              (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k),
              w r := by
            symm
            exact Finset.sum_card_fiberwise_eq_card_filter
              (Finset.univ : Finset (Fin (2 * N)))
              ((Finset.univ : Finset (Fin 10)).filter
                (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k)) g
      _ = ∑ r : Fin 10,
            if MME.StothersFourth.Phi233.pattern r i = k then
              w r else 0 := by
            exact Finset.sum_filter
              (fun r : Fin 10 ↦
                MME.StothersFourth.Phi233.pattern r i = k) w
  have hsigma0 := x.2.2 (0 : Fin 3) (0 : Fin 5)
  have hsigma2 := x.2.2 (0 : Fin 3) (2 : Fin 5)
  have hmuJ0 := x.2.2 (1 : Fin 3) (0 : Fin 5)
  have hmuJ3 := x.2.2 (1 : Fin 3) (3 : Fin 5)
  have hmuK0 := x.2.2 (2 : Fin 3) (0 : Fin 5)
  have hmuK3 := x.2.2 (2 : Fin 3) (3 : Fin 5)
  rw [hpartition 0 0] at hsigma0
  rw [hpartition 0 2] at hsigma2
  rw [hpartition 1 0] at hmuJ0
  rw [hpartition 1 3] at hmuJ3
  rw [hpartition 2 0] at hmuK0
  rw [hpartition 2 3] at hmuK3
  simp [MME.StothersFourth.Phi233.pattern,
    MME.StothersFourth.Phi233.marginalMultiplicity,
    MME.cwSquareBlockType, Fin.sum_univ_succ] at hsigma0 hsigma2 hmuJ0 hmuJ3 hmuK0 hmuK3
  have hsigma0' : w 0 + w 1 + w 2 = 2 * alpha + beta := by omega
  have hsigma2' : w 7 + w 8 + w 9 = 2 * alpha + beta := by omega
  refine ⟨g, hcoord, ?_⟩
  change
    (∑ r : Fin 10, w r) = 2 * N ∧
      w 0 + w 1 + w 2 = 2 * alpha + beta ∧
      w 7 + w 8 + w 9 = 2 * alpha + beta ∧
      w 3 + w 7 = alpha + gamma ∧
      w 2 + w 6 = alpha + gamma ∧
      w 6 + w 9 = alpha + gamma ∧
      w 0 + w 3 = alpha + gamma
  exact ⟨htotal, hsigma0', hsigma2', hmuJ0,
    hmuJ3, hmuK0, hmuK3⟩
