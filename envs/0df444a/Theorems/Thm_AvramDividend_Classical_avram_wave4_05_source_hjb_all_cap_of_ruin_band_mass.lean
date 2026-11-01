-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:37:27.183988+00:00
-- url     : https://prove2.me/theorems/7b849704-1b1b-4f50-bb9d-c416dabade06
-- title:
--   All-cap upper HJB under the exact source Levy ruin-band mass criterion
-- statement:
--   For the original source Levy process and any strict upper reserve at a finite optimal barrier, including zero, the full HJB holds if the drift plus explicit finite ruin-band compensation mass bound lies below the discounted barrier value. Source jump integrability is automatic.
-- source:
--   All-cap source overshoot upper HJB and source-only Levy ruin-band mass theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (hmass : X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
