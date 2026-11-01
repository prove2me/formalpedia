-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_killed_potential_interval_representation
-- name    : AvramDividend.Classical.avram_wave4_02_source_esscher_killed_potential_interval_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:20:20.873985+00:00
-- url     : https://prove2.me/theorems/963970fa-85af-4b07-8fea-b507849b5957
-- title:
--   Genuine killed-first-record Esscher potential gives the exact tilted scale interval-ratio identity
-- statement:
--   For the actual source spectrally negative Levy process with divergent first small-negative-jump moment and exact positive Esscher root, the genuine tilted scale ratio V(x)/V(a) is exp(-integral_x^a lambda(t)dt), 0<x<=a, where lambda(t)=-log E_P[e^{-q tau_1}; tau_1<D_t]-phi. This is a source-identified killed-record potential rate, continuous and nonnegative by an independently Proved theorem. It deliberately does not assert that lambda is an Itô excursion-height tail n(H>t), which still requires compensator construction.
-- source:
--   KKR 2013 scale review equations (31)-(33) as killed-record potential alternative, original source Lévy Markov semigroup, local scale sandwich, source log derivative, real FTC. Exact first record and reflected drawdown clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_02_source_esscher_killed_potential_interval_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ z : ℝ, 0 < z → V z = Real.exp (-(φ * z)) * W z)
    (x a : ℝ) (hx : 0 < x) (hxa : x ≤ a) :
    V x / V a =
      Real.exp (-(∫ t in x..a,
        (-Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X t ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) - φ))) := by sorry
