-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
-- name    : AvramDividend.Classical.avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:01:10.455072+00:00
-- url     : https://prove2.me/theorems/b9e2dab7-cfc7-4a0e-925b-da10c88b886e
-- title:
--   Original dividend rightLimit equals strict rightLim at every time
-- statement:
--   The original Avram definition rightLimit D(t) as an infimum over later dividend values agrees exactly, pathwise and for every time, with Mathlib's strict right limit of the monotone original admissible dividend path. This lets the original source and compensation quadrature proofs use the Mathlib one-sided limit API directly.
-- source:
--   Original DividendStrategy rightLimit definition and Mathlib Monotone.rightLim_eq_sInf with sInf_image'

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) (t : ℝ≥0) : rightLimit D t ω = Function.rightLim (fun s : ℝ≥0 => D s ω) t := by sorry
