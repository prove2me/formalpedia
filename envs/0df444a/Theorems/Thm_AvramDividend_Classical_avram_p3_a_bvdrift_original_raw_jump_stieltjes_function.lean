-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:34:00.314893+00:00
-- url     : https://prove2.me/theorems/835f5d6c-f812-4693-b877-cd033100004d
-- title:
--   Genuine original BV cumulative raw negative jumps form a Stieltjes function
-- statement:
--   For almost every sample path of the actual source spectrally negative bounded-variation Levy process, the complete finite-horizon cumulative raw negative jump magnitude is represented exactly as a nondecreasing right-continuous Stieltjes function. Its jumps are the genuine original left-limit jumps, not an auxiliary compound Poisson model. The statement imposes no additional representation assumptions.
-- source:
--   Uses Proved original real-jump right convergence 49bf9876, new direct real-jump monotonicity and deterministic right-to-within bridge. Constructs pinned Mathlib StieltjesFunction.mk from monotone and continuous-within-Ici evidence, with exact equality for the original raw real sum.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0, ∀ t : ℝ≥0,
      F t = (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
