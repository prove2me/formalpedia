-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_finite_barrier_boundary_nonneg
-- name    : AvramDividend.Classical.avram_sweep17_vcstar_finite_barrier_boundary_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:01:04.27291+00:00
-- url     : https://prove2.me/theorems/b0bf9e44-e274-43ae-858a-cc19f1aa3f76
-- title:
--   Nonnegative vcstar at any finite canonical barrier without extra smoothness
-- statement:
--   For the original spectrally negative Levy process and q-scale function with finite cstar, vcstar at the real canonical barrier is nonnegative, including cstar=0. At zero this follows from the already Proved original zero-barrier boundary value. At positive cstar it follows from nonnegative W and the Proved nonnegative scale derivative, with the true barrierValue quotient definition. No root C2/Gaussian/BV disjunction is required.
-- source:
--   Proved original scaleDeriv_nonneg UUID 3f19a0fb-a939-4bf4-8dd7-0f4b6a047b68 and barrier_zero_boundary_value_nonneg UUID df5df3b8-8ec5-4231-85d3-2263c3b9e822; positive-cap quotient branch copied from source exact 8ce07d6a candidate and pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg


open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_vcstar_finite_barrier_boundary_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    0 ≤ vcstar W (cstar W).toReal := by sorry
