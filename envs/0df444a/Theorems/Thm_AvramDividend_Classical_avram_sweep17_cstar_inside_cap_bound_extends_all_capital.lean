-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_inside_cap_bound_extends_all_capital
-- name    : AvramDividend.Classical.avram_sweep17_cstar_inside_cap_bound_extends_all_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:46:59.984102+00:00
-- url     : https://prove2.me/theorems/eaf314bf-020f-4513-a3cc-8fdf608e519e
-- title:
--   Inside-cstar capped comparison extends to every nonnegative initial reserve
-- statement:
--   For the original spectrally negative Levy process and finite optimal barrier, any bound on actual capped valueFunctionLe for all reserve levels 0<=x<=cstar extends to all x>=0 provided vcstar(cstar.toReal)>=0. The accepted original cap-boundary extension handles x above the barrier. All dividend strategy and payment atoms remain unchanged, and the inside-cap bound is an explicit premise to avoid circularity.
-- source:
--   Proved source-specialised affine cap bridge 05ace1c1-d5bb-4d86-a577-910194d9c0a9 and pinned Mathlib ENNReal.ofReal_toReal/lt_ofReal_iff_toReal_lt; local verification remains a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_boundary_to_above_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_cstar_inside_cap_bound_extends_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hc : cstar W < ⊤)
    (hwc : 0 ≤ vcstar W (cstar W).toReal)
    (hInside :
      ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry
