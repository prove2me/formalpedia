-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
-- name    : AvramDividend.Classical.avram_sweep17_cstar_capped_value_all_capital_without_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:14:01.677582+00:00
-- url     : https://prove2.me/theorems/b706a956-9e70-4a52-a033-2a0c56beaf14
-- title:
--   Extend original cstar capped value comparison globally without any root smoothness condition
-- statement:
--   For the original spectrally negative Lévy process and finite cstar, an exact bound on the capped valueFunctionLe inside cstar extends to all nonnegative initial reserve, assuming only original standing/scale hypotheses, with no Gaussian, bounded-variation or C2 smoothness disjunction. It follows by the already Proved global vcstar nonnegativity and exact affine cap extension.
-- source:
--   Proved original scale-function global nonnegativity 494b2f23-1b63-435d-a80e-16168cee645e and Proved cap extension eaf314bf-020f-4513-a3cc-8fdf608e519e under pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_inside_cap_bound_extends_all_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_cstar_capped_value_all_capital_without_smoothness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hInside :
      ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by sorry
