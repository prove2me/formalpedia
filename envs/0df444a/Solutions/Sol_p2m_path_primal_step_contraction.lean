-- Prove2me | solution 1 for p2m_path_primal_step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:06:47.225095+00:00
-- url     : https://prove2.me/submissions/5423e224-0f1d-4c20-b3a0-2257238cb780

import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_primal_update
import Theorems.Thm_p2m_path_norm1_smul
import Theorems.Thm_p2m_path_norm1_nonneg
import Theorems.Thm_p2m_path_stepLength_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (ht : t ≤ stepLength r p d) :
    norm1 (primalInfeas A b p') ≤ (1 - t) * norm1 (primalInfeas A b p) := by
  have hθ1 := p2m_path_stepLength_le_one r p d
  have hfac0 : 0 ≤ 1 - stepLength r p d := by linarith
  have hfac : 1 - stepLength r p d ≤ 1 - t := by linarith
  rw [p2m_path_primal_update A b c δ r hδ0 hδ1 hr0 hr1 p d p' hstep]
  rw [p2m_path_norm1_smul _ hfac0]
  exact mul_le_mul_of_nonneg_right hfac (p2m_path_norm1_nonneg _)
end
