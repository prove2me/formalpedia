-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
-- name    : AvramDividend.Classical.avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:54:17.331594+00:00
-- url     : https://prove2.me/theorems/31a30bff-51af-487c-9fbb-ae2a31f9d83b
-- title:
--   Original same-reserve level dividend Stieltjes interval equals finite-variation drift increment
-- statement:
--   For the actual original spectrally negative Lévy process X and admissible original dividend D, suppose the original prepayment controlled reserve is the same real value k at endpoints a≤b, the right dividend atom vanishes at each endpoint, and the original X increment equals drift times elapsed time (for example on a finite-activity no-negative-mark path). Then the original dividend Stieltjes measure of (a,b] equals ENNReal.ofReal(drift*(b-a)). This generalises the Proved zero-reserve endpoint Stieltjes identity 28a916cf to arbitrary constant reserve levels, especially the upper finite reserve cap.
-- source:
--   Exact original Stieltjes formula dividendMeasure_Ioc_rightLimit Proved and zero-reserve source 28a916cf Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb29_original_constant_pre_right_reserve_stieltjes_exact_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (k : ℝ)
    (ha : riskProcess X x D a ω = k)
    (hb : riskProcess X x D b ω = k)
    (hAtomA : rightLimit D a ω = D a ω)
    (hAtomB : rightLimit D b ω = D b ω)
    (hLine : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by sorry
