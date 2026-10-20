-- Prove2me | solution 1 for p2m_dual_step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:34:22.735845+00:00
-- url     : https://prove2.me/submissions/9b9a095d-a907-4582-a641-8c2a4998818e

import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_dual_update
import Theorems.Thm_p2m_norm1_smul
import Theorems.Thm_p2m_norm1_nonneg
import Theorems.Thm_p2m_stepLength_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing
theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (ht : t ≤ stepLength r p d) :
    norm1 (dualInfeas A c p') ≤ (1 - t) * norm1 (dualInfeas A c p) := by
  have hθ1 := p2m_stepLength_le_one r p d
  have hfac0 : 0 ≤ 1 - stepLength r p d := by linarith
  have hfac : 1 - stepLength r p d ≤ 1 - t := by linarith
  rw [p2m_dual_update A b c δ r hδ0 hδ1 hr0 hr1 p d p' hstep]
  rw [p2m_norm1_smul _ hfac0]
  exact mul_le_mul_of_nonneg_right hfac (p2m_norm1_nonneg _)
