-- Prove2me | solution 1 for singular_value_le_schatten_norm
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:41:14.07963+00:00
-- url     : https://prove2.me/submissions/a1d4493d-0214-4545-b5e8-0fe19998d8fc

import Definitions.Def_matrix_completion_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MatrixCompletion
open scoped BigOperators

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) (k : Fin n₂),
      1 ≤ q →
      (Matrix.toEuclideanLin X).singularValues (k : ℕ) ≤ schattenNorm q X := by
  intro n₁ n₂ q X k hq
  set T := Matrix.toEuclideanLin X with hT
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le one_pos hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hσnn : ∀ j : ℕ, 0 ≤ T.singularValues j := fun j => T.singularValues_nonneg j
  have hσk : 0 ≤ T.singularValues (k:ℕ) := hσnn k
  have hinv_nonneg : 0 ≤ q⁻¹ := by positivity
  have h2 : T.singularValues (k:ℕ) = Real.rpow (Real.rpow (T.singularValues (k:ℕ)) q) q⁻¹ :=
    (Real.rpow_rpow_inv hσk hqne).symm
  have h3 : Real.rpow (T.singularValues (k:ℕ)) q
      ≤ ∑ j : Fin n₂, Real.rpow (T.singularValues (j:ℕ)) q := by
    have := Finset.single_le_sum
      (f := fun j : Fin n₂ => Real.rpow (T.singularValues (j:ℕ)) q)
      (fun j _ => Real.rpow_nonneg (hσnn _) _) (Finset.mem_univ k)
    simpa using this
  have h4 : Real.rpow (Real.rpow (T.singularValues (k:ℕ)) q) q⁻¹ ≤ schattenNorm q X := by
    show Real.rpow (Real.rpow (T.singularValues (k:ℕ)) q) q⁻¹
      ≤ Real.rpow (∑ j : Fin n₂, Real.rpow (T.singularValues (j:ℕ)) q) q⁻¹
    exact Real.rpow_le_rpow (Real.rpow_nonneg hσk _) h3 hinv_nonneg
  calc T.singularValues (k:ℕ)
      = Real.rpow (Real.rpow (T.singularValues (k:ℕ)) q) q⁻¹ := h2
    _ ≤ schattenNorm q X := h4
