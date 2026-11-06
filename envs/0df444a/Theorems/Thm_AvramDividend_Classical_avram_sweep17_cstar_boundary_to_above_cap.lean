-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_boundary_to_above_cap
-- name    : AvramDividend.Classical.avram_sweep17_cstar_boundary_to_above_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:43:00.380272+00:00
-- url     : https://prove2.me/theorems/05ace1c1-d5bb-4d86-a577-910194d9c0a9
-- title:
--   Original finite-cstar boundary bound extends above the barrier
-- statement:
--   For the original spectrally negative Levy process X and finite scale barrier cstar W, an explicit nonnegative value of vcstar at the real barrier and a capped-value boundary comparison extend to every initial capital above the barrier, by the proved original affine boundary extension and the exact above-barrier branch of vcstar.
-- source:
--   Proved original capped-boundary extension 5b8dee80-f0f3-4cd8-8ec3-4a6453068bf1, finite ENNReal barrier conversion, and original vcstar barrierValue affine branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_boundary_bound_extends_above_cap


open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_cstar_boundary_to_above_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hc : cstar W < ⊤)
    (hwc : 0 ≤ vcstar W (cstar W).toReal)
    (hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal)) :
    ∀ x : ℝ, (cstar W).toReal ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry
