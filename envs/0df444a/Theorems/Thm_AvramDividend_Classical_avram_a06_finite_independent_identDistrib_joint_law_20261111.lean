-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_finite_independent_identDistrib_joint_law_20261111
-- name    : AvramDividend.Classical.avram_a06_finite_independent_identDistrib_joint_law_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:11:28.163583+00:00
-- url     : https://prove2.me/theorems/14e64e14-ed8e-4b57-ae26-807825ca7576
-- title:
--   Two independent finite families with coordinatewise identical laws have identical joint laws
-- statement:
--   Finite independent random families with the same marginal law at every coordinate have the same full joint law. Use the Prove2Me-pinned Mathlib iIndepFun.map_fun_eq_pi_map theorem and coordinatewise IdentDistrib.map_eq. This bridges IID deterministic shifted mark blocks to prefix-block laws for the A06 conditional Fourier formula 5d7ad8be.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_finite_independent_identDistrib_joint_law_20261111
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (U V : Fin n → Ω → A)
    (hU : ∀ i, Measurable (U i)) (hV : ∀ i, Measurable (V i))
    (hIndU : iIndepFun U P) (hIndV : iIndepFun V P)
    (hLaw : ∀ i, IdentDistrib (U i) (V i) P P) :
    IdentDistrib (fun ω => fun i : Fin n => U i ω)
      (fun ω => fun i : Fin n => V i ω) P P := by sorry
