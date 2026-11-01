-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_stopped_record_exponential_normalisation
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_stopped_record_exponential_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:20:49.666858+00:00
-- url     : https://prove2.me/theorems/a8da6c5c-d72c-4a14-b4d7-3bfbff27ee7e
-- title:
--   True Esscher stopped-record normalisation is a positive subunit exponential height survival law
-- statement:
--   For the actual original spectrally negative Levy path, exact q-discounted first-upward-record survival before reflected drawdown ruin, and positive Esscher root psi(phi)=q, the stopped Esscher-weighted factor e^{phi h} E_P[e^{-q tau_h};tau_h<D_a] equals e^{-h lambda(a)}, where lambda(a)=-log E_P[e^{-q tau_1};tau_1<D_a]-phi is continuous and nonnegative. At every a,h>0 this factor is strictly positive and <=1. Source-specific exact local-time normalization; not yet an excursion PPP theorem.
-- source:
--   Genuine original-Lévy stopped-record strong-Markov exponential hazard 1f5b13d3 and source Esscher rate nonnegativity 08f9ec73; no positive overshoot at records; KKR 2013 local-time-normalized excursion hazard.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_stopped_record_exponential_normalisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    let G := Real.exp (φ * h) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal
    let rate := -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ
    0 < G ∧ G = Real.exp (-(h * rate)) ∧ G ≤ 1 := by sorry
