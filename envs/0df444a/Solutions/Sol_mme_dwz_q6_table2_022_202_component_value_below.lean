-- Prove2me | solution 1 for mme_dwz_q6_table2_022_202_component_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:21:26.656389+00:00
-- url     : https://prove2.me/submissions/a7f0a137-b6a0-4d94-8bb2-95c32073e64a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
import Theorems.Thm_mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
import Theorems.Thm_mme_dwz_q6_table2_022_component_power_le_dimension
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open Filter Topology
open MME BigOperators MME.DWZSquare MME.DWZTable2Component022

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (9 : Fin 15)) :
    HasTauValueAtLeast
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 0 2 2)) tau V ∧
      HasTauValueAtLeast
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 2 0 2)) tau V := by
  have htau0 : 0 ≤ tau := by linarith
  let B : ℝ := componentBase tau (9 : Fin 15)
  let C : ℝ := 155520 * tau
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgap0 :=
    mme_strict_pow_absorbs_sqrt_exp_loss V B C hV
      (by simpa only [B] using hVlt) hC
  let s : ℕ → ℕ := fun n => table2Power022 (n + 1)
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [s, table2Power022]
    omega
  have hgap :
      ∀ᶠ n : ℕ in atTop,
        V ^ (s n) ≤ B ^ (s n) *
          Real.exp (-C * Real.sqrt ((((s n) + 1 : ℕ) : ℝ))) :=
    hs.eventually hgap0
  have hfinite :
      ∀ᶠ n : ℕ in atTop,
        let t := n + 1
        let m := table2Power022 t
        let L := table2OuterCount022 t
        let G := table2MiddleCount022 t
        let D := Nat.card (Restricted022Word 6 m L G)
        (TensorObj.Restrict
            (MMObj K 1 1 D)
            (((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 0 2 2)).kronPow m) ∧
          TensorObj.Restrict
            (MMObj K D 1 1)
            (((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 2 0 2)).kronPow m)) ∧
          V ^ m ≤ (D : ℝ) ^ tau := by
    filter_upwards [hgap] with n hgapn
    dsimp only [s] at hgapn
    dsimp only
    have ht : 0 < n + 1 := by omega
    let m := table2Power022 (n + 1)
    let L := table2OuterCount022 (n + 1)
    let G := table2MiddleCount022 (n + 1)
    let D := Nat.card (Restricted022Word 6 m L G)
    have hinput :=
      mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
        (K := K) tau (n + 1) ht
    dsimp only at hinput
    have hcomponent :=
      mme_dwz_q6_table2_022_component_power_le_dimension
        tau htau0 (n + 1) ht
    dsimp only at hcomponent
    have hpoly :=
      mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt tau htau0 m
    have hrate :
        B ^ m ≤
          Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
            (D : ℝ) ^ tau := by
      calc
        B ^ m = componentBase tau (9 : Fin 15) ^ m := by rfl
        _ ≤ ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau *
              (D : ℝ) ^ tau := by
          simpa only [m, L, G, D] using hcomponent
        _ ≤ Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
              (D : ℝ) ^ tau := by
          apply mul_le_mul_of_nonneg_right
          · simpa only [C] using hpoly
          · positivity
    have hVdim : V ^ m ≤ (D : ℝ) ^ tau := by
      calc
        V ^ m ≤ B ^ m *
            Real.exp (-C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) := by
          simpa only [m] using hgapn
        _ ≤ (Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
              (D : ℝ) ^ tau) *
            Real.exp (-C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hrate (Real.exp_pos _).le
        _ = (D : ℝ) ^ tau := by
          have hcancel :
              Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
                  Real.exp (-C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) = 1 := by
            rw [← Real.exp_add]
            ring_nf
            exact Real.exp_zero
          calc
            (Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
                (D : ℝ) ^ tau) *
                Real.exp (-C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) =
              (Real.exp (C * Real.sqrt ((((m + 1 : ℕ) : ℝ)))) *
                Real.exp (-C * Real.sqrt ((((m + 1 : ℕ) : ℝ))))) *
                (D : ℝ) ^ tau := by ring
            _ = (D : ℝ) ^ tau := by rw [hcancel, one_mul]
    exact ⟨hinput.1, hVdim⟩
  constructor
  · apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType 0 2 2)) tau V hV s hs
      (fun _ => (0 : ℝ)) tendsto_const_nhds
    filter_upwards [hfinite] with n hn
    dsimp only at hn
    let D := Nat.card
      (Restricted022Word 6 (table2Power022 (n + 1))
        (table2OuterCount022 (n + 1))
        (table2MiddleCount022 (n + 1)))
    refine ⟨1, (fun _ : Fin 1 => 1), (fun _ : Fin 1 => 1),
      (fun _ : Fin 1 => D), ?_, ?_⟩
    · simpa only [TensorObj.bigAdd] using hn.1.1
    · simp only [sub_zero, mul_one, Fin.sum_univ_one, Nat.one_mul]
      simpa only [D] using hn.2
  · apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType 2 0 2)) tau V hV s hs
      (fun _ => (0 : ℝ)) tendsto_const_nhds
    filter_upwards [hfinite] with n hn
    dsimp only at hn
    let D := Nat.card
      (Restricted022Word 6 (table2Power022 (n + 1))
        (table2OuterCount022 (n + 1))
        (table2MiddleCount022 (n + 1)))
    refine ⟨1, (fun _ : Fin 1 => D), (fun _ : Fin 1 => 1),
      (fun _ : Fin 1 => 1), ?_, ?_⟩
    · simpa only [TensorObj.bigAdd] using hn.1.2
    · simp only [sub_zero, mul_one, Fin.sum_univ_one]
      simpa only [D] using hn.2
