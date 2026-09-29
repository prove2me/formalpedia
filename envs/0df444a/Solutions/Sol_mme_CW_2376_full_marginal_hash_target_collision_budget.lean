-- Prove2me | solution 1 for mme_CW_2376_full_marginal_hash_target_collision_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:40:43.546749+00:00
-- url     : https://prove2.me/submissions/76ede846-d2d9-4a4f-9c96-4dec5350f920

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_CW_2376_marginal_hash_state
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
import Theorems.Thm_mme_CW_2376_full_marginal_star_degree_le_explicit
import Theorems.Thm_mme_CW_2376_marginal_star_card_le_five_pow
import Theorems.Thm_mme_CW_2376_exact_target_count_factorization
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_CW_2376_prime_hash_collision_margin
import Theorems.Thm_mme_CW_2376_hash_budget_of_degree

open MME BigOperators Filter

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem positive_uniform_degree_choice
    {alpha iota : Type*} [DecidableEq alpha] [Fintype iota]
    (T : Finset alpha) (degree : iota → alpha → ℕ) (B C : ℕ)
    (hB1 : 1 ≤ B) (hC1 : 1 ≤ C)
    (hB : ∀ i, ∀ a ∈ T, degree i a ≤ B)
    (hC : ∀ i, ∀ a ∈ T, degree i a ≤ C) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ B ∧ D ≤ C ∧
      ∀ i, ∀ a ∈ T, degree i a ≤ D := by
  classical
  let P : Finset (iota × alpha) := Finset.univ.product T
  let M : ℕ := P.sup (fun ia => degree ia.1 ia.2)
  refine ⟨max 1 M, Nat.le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le hB1
    apply Finset.sup_le
    intro ia hia
    exact hB ia.1 ia.2 (Finset.mem_product.mp hia).2
  · apply max_le hC1
    apply Finset.sup_le
    intro ia hia
    exact hC ia.1 ia.2 (Finset.mem_product.mp hia).2
  · intro i a ha
    exact (Finset.le_sup
      (show (i, a) ∈ P by
        exact Finset.mem_product.mpr ⟨Finset.mem_univ i, ha⟩)).trans
      (Nat.le_max_right 1 M)

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      ∃ E : Finset (CW2376MarginalSupportedAddress m),
        CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  classical
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < m := by omega
  let N := cw2376ProfileLength m
  let Dstar := cw2376TargetStarDegree m
  let B := (N + 1) ^ 15 * Dstar
  let C := 5 ^ N
  let degree : Fin 3 → CW2376MarginalSupportedAddress m → ℕ :=
    fun i a => ((cw2376MarginalSupportedUniverse m).filter
      (fun b => b.1 i = a.1 i)).card
  let V : ℝ :=
    (N.factorial : ℝ) /
      (((384072 * m).factorial : ℝ) *
        ((1308290 * m).factorial : ℝ) *
        ((1231903 * m).factorial : ℝ) *
        ((75036 * m).factorial : ℝ) *
        ((699 * m).factorial : ℝ))
  let loss : ℝ := Real.exp
    (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ)))

  have hfactor := mme_CW_2376_exact_target_count_factorization m
  have hprodReal :
      (∏ r : Fin 5,
          ((cw2376MarginalMultiplicity m r).factorial : ℝ)) =
        ((384072 * m).factorial : ℝ) *
          ((1308290 * m).factorial : ℝ) *
          ((1231903 * m).factorial : ℝ) *
        ((75036 * m).factorial : ℝ) *
          ((699 * m).factorial : ℝ) := by
    rw [show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by decide]
    simp [cw2376MarginalMultiplicity, mul_assoc]
  have hT : ((cw2376AllExactTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ) := by
    simpa only [N, V, Dstar, hprodReal] using hfactor.1
  have hDstar1 : 1 ≤ Dstar := by
    simpa only [Dstar] using hfactor.2
  have hB1 : 1 ≤ B := by
    have hpw : 1 ≤ (N + 1) ^ 15 :=
      Nat.one_le_pow 15 (N + 1) (by omega)
    have := Nat.mul_le_mul hpw hDstar1
    simpa only [one_mul, B] using this
  have hC1 : 1 ≤ C := by
    simpa only [C] using Nat.one_le_pow N 5 (by omega : 0 < (5 : ℕ))
  have hBdeg : ∀ i, ∀ a ∈ cw2376AllExactTargetEdges m,
      degree i a ≤ B := by
    intro i a ha
    simpa only [degree, B, N, Dstar, cw2376TargetStarDegree] using
      mme_CW_2376_full_marginal_star_degree_le_explicit m hmpos a i
  have hCdeg : ∀ i, ∀ a ∈ cw2376AllExactTargetEdges m,
      degree i a ≤ C := by
    intro i a ha
    simpa only [degree, C, N] using
      mme_CW_2376_marginal_star_card_le_five_pow m i a
  obtain ⟨D, hD1, hDdom, hD5, hdeg⟩ :=
    positive_uniform_degree_choice
      (cw2376AllExactTargetEdges m) degree B C hB1 hC1 hBdeg hCdeg
  obtain ⟨p, hpPrime, hp5, S, hSrange, hSfree, hSlarge, hpBound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree N D hD1
      (by simpa only [C] using hD5)
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpodd : Odd p := hpPrime.odd_of_ne_two (by omega)
  have hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) := by
    apply mme_CW_2376_prime_hash_collision_margin N D Dstar p S.card hD1
    · simpa only [B] using hDdom
    · exact hSlarge
    · exact hpBound
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  obtain ⟨E, hclosed, hbudget⟩ :=
    mme_CW_2376_hash_budget_of_degree
      m p D Dstar hmpos hp5 hpodd S hSrange hSfree V loss hV hT
      (by
        intro i a ha
        exact hdeg i a ha)
      hmargin
  exact ⟨E, hclosed, by simpa only [N, V, loss] using hbudget⟩
