-- Prove2me | solution 1 for d9_integral_independent_prefix_suffix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:10:07.479184+00:00
-- url     : https://prove2.me/submissions/29b76f1e-b7b6-4371-b3f6-186024596844

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (j k : ℕ)
    (F : (Finset.Icc 1 j → ℝ) → ℝ)
    (G : (Finset.Icc (j + 1) (k + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFint : Integrable (fun ω => F (fun i => X i.1 ω)) P) :
    ∫ ω, F (fun i => X i.1 ω) * G (fun i => X i.1 ω) ∂P =
      (∫ ω, F (fun i => X i.1 ω) ∂P) *
        (∫ ω, G (fun i => X i.1 ω) ∂P) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 j
  let T : Finset ℕ := Finset.Icc (j + 1) (k + 1)
  let U : Ω → S → ℝ := fun ω i => X i.1 ω
  let V : Ω → T → ℝ := fun ω i => X i.1 ω
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hi hmem
    have hleft : i ≤ j := (Finset.mem_Icc.mp (by simpa [S] using hi)).2
    have hright : j + 1 ≤ i := (Finset.mem_Icc.mp (by simpa [T] using hmem)).1
    omega
  have hTuple : IndepFun U V P :=
    iIndepFun.indepFun_finset S T hST hM.indep hM.meas
  have hInd : IndepFun (fun ω => F (U ω)) (fun ω => G (V ω)) P :=
    hTuple.comp hF hG
  have hfactor := hInd.integral_fun_mul_eq_mul_integral
    hFint.aestronglyMeasurable (hG.comp (by
      apply measurable_pi_iff.mpr
      intro i
      exact hM.meas i.1)).aestronglyMeasurable
  simpa [U, V] using hfactor
