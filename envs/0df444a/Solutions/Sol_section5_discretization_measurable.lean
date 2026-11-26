-- Prove2me | solution 1 for section5_discretization_measurable
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:51.358344+00:00
-- url     : https://prove2.me/submissions/5f6a1912-3774-42e5-aadb-7b14051a824c

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n M : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)) := by
  have hmround : Measurable (roundVec M : EuclideanSpace ℝ (Fin n) → _) := by
    unfold roundVec
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply measurable_pi_lambda
    intro i
    unfold roundCoord
    apply Measurable.add measurable_const
    apply Measurable.const_mul
    apply (measurable_of_countable (fun k : ℤ => (k:ℝ))).comp
    fun_prop
  have hltf : Measurable (ltf w 0) := by
    unfold ltf sgn
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_le measurable_const (by fun_prop)
  have hcast : Measurable (fun k : ℤ => (k:ℝ)) := measurable_of_countable _
  exact (hcast.comp (hltf.sub (hltf.comp hmround))).pow_const 2
