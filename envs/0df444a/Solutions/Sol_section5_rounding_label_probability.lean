-- Prove2me | solution 1 for section5_rounding_label_probability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:25.242198+00:00
-- url     : https://prove2.me/submissions/6c21e6b3-c11d-4e84-baa0-48986566eb9b

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Mathlib
import Theorems.Thm_section5_discretization_integral_bound
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! Gaussian orientation errors after coordinate rounding, using the mission's already-Proved
Gaussian disagreement lemma (Lemma 2.1), with its accepted proof checked locally. -/

theorem section5_ltf_measurable {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Measurable (ltf w θ) := by
  unfold ltf sgn
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    measurable_const measurable_const

theorem section5_roundVec_measurable (n M : ℕ) :
    Measurable (roundVec M : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold roundVec roundCoord
  fun_prop







end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n M : ℕ} (hM : 1 ≤ M)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 x ≠ ltf w 0 (roundVec M x)} ≤ Real.sqrt (8*n/M) := by
  let S := {x | ltf w 0 x ≠ ltf w 0 (roundVec M x)}
  have hs : MeasurableSet S := (measurableSet_eq_fun (section5_ltf_measurable w 0)
    ((section5_ltf_measurable w 0).comp (section5_roundVec_measurable n M))).compl
  have heq : (fun x => (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)) =
      S.indicator (fun _ => (4:ℝ)) := by
    funext x
    simp only [S,Set.indicator_apply,Set.mem_ofPred_eq]
    unfold ltf sgn
    split_ifs <;> norm_num at *
  have hi := section5_discretization_integral_bound hM w hw
  rw [heq,integral_indicator hs,setIntegral_const] at hi
  change (stdGaussian (EuclideanSpace ℝ (Fin n))).real S ≤ _
  change (stdGaussian (EuclideanSpace ℝ (Fin n))).real S * 4 ≤ _ at hi
  linarith
