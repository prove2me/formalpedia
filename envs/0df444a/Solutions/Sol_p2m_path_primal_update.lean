-- Prove2me | solution 1 for p2m_path_primal_update
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:36:57.048113+00:00
-- url     : https://prove2.me/submissions/68e420ca-5ee9-42c0-8026-e4ee9c5cda20

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
open scoped VanderbeiLP.PathFollowing in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (p d p' : PDPoint m n)
    (hstep : IsPathFollowingStep A b c δ r p d p') :
    primalInfeas A b p' = (1 - stepLength r p d) • primalInfeas A b p := by
  rcases hstep with ⟨_, hdir, hnext⟩
  have hprimal := hdir.1
  simp [primalInfeas] at hprimal
  set θ := stepLength r p d
  rw [hnext]
  simp [primalInfeas, PDPoint.advance, Matrix.mulVec_add, Matrix.mulVec_smul, θ]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hpi := congrFun hprimal i
  simp [primalInfeas] at hpi
  linear_combination -θ * hpi
end
