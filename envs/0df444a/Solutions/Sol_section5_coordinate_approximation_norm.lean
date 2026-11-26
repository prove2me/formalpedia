-- Prove2me | solution 1 for section5_coordinate_approximation_norm
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:56.152905+00:00
-- url     : https://prove2.me/submissions/4f05b635-d748-4434-91ea-75db317cc740

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i, |x i-y i| ≤ δ) : ‖x-y‖ ≤ δ*Real.sqrt n := by
  have hs : ‖x-y‖^2 ≤ (n:ℝ)*δ^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, δ^2 := by
        apply Finset.sum_le_sum
        intro i hi
        change ‖x i-y i‖^2 ≤ δ^2
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = _ := by simp
  have hpos : 0 ≤ δ*Real.sqrt n := mul_nonneg hδ (Real.sqrt_nonneg _)
  have heq : (δ*Real.sqrt n)^2=(n:ℝ)*δ^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  nlinarith [norm_nonneg (x-y)]
