-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
-- name    : AvramDividend.Classical.avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:21:28.857993+00:00
-- url     : https://prove2.me/theorems/9f3b0f54-d443-4d8d-858e-2c7e375604f4
-- title:
--   Esscher log-derivative flatness transfers to the actual reflected-killed first-record asymptotic hazard
-- statement:
--   A source-faithful bridge needed by the genuine original-process large-drawdown hazard theorem. Under the original infinite-small-negative-jump hypothesis and a positive Esscher root, the proved stopped-record identity differentiates log V to the actual killed first-record hazard minus φ. If the Esscher-tilted log derivative tends to zero at infinity, the actual stopped first-record hazard tends to φ. No Standing hypothesis and no replacement of either clock.
-- source:
--   Proved source identity AvramDividend.Classical.avram_wave4_02_source_esscher_record_log_derivative (eb85f6af-2ff4-408d-a3be-c9521c82a2ef) and Real Filter tendsto algebra. This child is a formal dependency of parent d455bcb7-c70c-47a4-b83d-cc0d689003b6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hflat : Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      atTop (nhds φ) := by sorry
