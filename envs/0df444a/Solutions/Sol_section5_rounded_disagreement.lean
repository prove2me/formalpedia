-- Prove2me | solution 1 for section5_rounded_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:41.461392+00:00
-- url     : https://prove2.me/submissions/501f46aa-e384-4ddc-ac84-edc39e22ed76

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_ltf
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_rounding_label_probability
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n M : ℕ} (hM : 1 ≤ M)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 (roundVec M x) ≠ ltf u 0 (roundVec M x)} ≤
        ‖w-u‖/2+2*Real.sqrt (8*n/M) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let S := {x | ltf w 0 x ≠ ltf u 0 x}
  let A := {x | ltf w 0 x ≠ ltf w 0 (roundVec M x)}
  let B := {x | ltf u 0 x ≠ ltf u 0 (roundVec M x)}
  have hsubset : {x | ltf w 0 (roundVec M x) ≠ ltf u 0 (roundVec M x)} ⊆ S ∪ (A ∪ B) := by
    intro x hx
    by_contra h
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_not,S,A,B] at h
    exact hx (h.2.1.symm.trans (h.1.trans h.2.2))
  have hcont : μ.real S ≤ ‖w-u‖/2 := by
    simpa [μ,S,disagree,measureReal_def] using
      (section5_gaussian_disagreement_proved w u hw hu 0 0).1
  have hA := section5_rounding_label_probability hM w hw
  have hB := section5_rounding_label_probability hM u hu
  calc
    _ ≤ μ.real (S ∪ (A ∪ B)) := measureReal_mono hsubset
    _ ≤ μ.real S+(μ.real A+μ.real B) :=
      (measureReal_union_le _ _).trans (add_le_add (le_refl _) (measureReal_union_le _ _))
    _ ≤ _ := by linarith
