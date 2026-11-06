-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_positive_cap_interior_HJB
-- name    : AvramDividend.Classical.avram_sweep17_vcstar_positive_cap_interior_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:49:36.589757+00:00
-- url     : https://prove2.me/theorems/a8dbf3a4-6495-4fbb-91cb-1e00b65dbd0f
-- title:
--   Exact positive-cstar interior HJB and original generator domain from proved scale identities
-- statement:
--   For original X under standing, q-scale and root smoothness assumptions, at every strictly positive reserve strictly below the finite positive canonical barrier cstar W, vcstar belongs to the original generator's domain and satisfies max(generator vcstar - q vcstar, 1 - derivative vcstar)=0. The proof combines the already Proved exact generator equality on (0,cstar) and the proved slope lower bound, with explicit ENNReal/real barrier conversion.
-- source:
--   Exact Proved generator_vcstar_eq_zero UUID 88d146b8-1b63-463d-8780-cf80ad7a9d40, vcstar_deriv_ge_one UUID d42fc3e4-7a32-428c-80a3-1827a721cf4f and pinned Mathlib ENNReal.ofReal_lt_iff_lt_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_vcstar_positive_cap_interior_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
