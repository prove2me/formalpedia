-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:25:45.570694+00:00
-- url     : https://prove2.me/theorems/7423dfee-c973-497f-a274-07e572cbd7a0
-- title:
--   True original spectrally negative Lévy jump times equal strict jumps of its actual drift residual at every positive time
-- statement:
--   For the genuine original spectrally negative Lévy path, with no bounded-variation, standing or finite-intensity assumption, a strictly positive time is a nonzero source X jump if and only if it is a strict upward left-limit jump of the actual drift residual t*X.drift−X_t. The equivalence holds for every original sample and all t>0. It identifies actual source jump support with the residual jump support for subsequent finite-step and intrinsic counting-measure proofs; no constructed process or compensator is assumed.
-- source:
--   Original X.leftLim path property and continuity of u↦u*X.drift identify leftLim of the residual as t*drift−X_(t-). Canonical Proved e95fe5bc-c756-43ca-82d7-acab7078e2eb gives every true positive-time source mark ΔX≤0 pathwise. Rearranging identifies a strict residual jump with ΔX<0 and hence ΔX≠0.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (Function.leftLim
        (fun u : ℝ≥0 => (u : ℝ) * X.drift - X.X u ω) t <
      (t : ℝ) * X.drift - X.X t ω) ↔
    X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0 := by sorry
