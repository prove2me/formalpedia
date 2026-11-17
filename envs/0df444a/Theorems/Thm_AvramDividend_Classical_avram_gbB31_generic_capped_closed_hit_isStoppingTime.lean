-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_generic_capped_closed_hit_isStoppingTime
-- name    : AvramDividend.Classical.avram_gbB31_generic_capped_closed_hit_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:02:17.690581+00:00
-- url     : https://prove2.me/theorems/56a9a86f-d80a-4554-9937-d09d56011bd1
-- title:
--   Generic adapted right-continuous upper-semicontinuous process capped closed hitting stopping time
-- statement:
--   For an adapted right-continuous real stochastic process with paths upper semicontinuous on compact horizons, prove the first hitting time of any upper closed threshold [x,infinity) capped by H is a stopping time. This generalises the original reflected supremum result to negative risk-process paths, directly addressing the Gaussian lower cutoff-clock obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_generic_capped_closed_hit_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (U : ℝ≥0 → Ω → ℝ) (hAdapt : Adapted 𝓕 U)
    (hRight : ∀ ω (u : ℝ≥0),
      ContinuousWithinAt (fun t => U t ω) (Ici u) u)
    (hUSC : ∀ ω (t : ℝ≥0),
      UpperSemicontinuousOn (fun u => U u ω) (Icc 0 t))
    (S : Set ℝ≥0) (hS : S.Countable)
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => U u ω) ⁻¹' Ici x) ∪ {H}))) := by sorry
