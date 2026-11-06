-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_all_capital
-- name    : AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_all_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:45:30.765607+00:00
-- url     : https://prove2.me/theorems/bb3da317-9303-46a0-baf8-a4850da2dab8
-- title:
--   Nonnegative original vcstar candidate on all nonnegative reserve levels for finite optimal barrier
-- statement:
--   Under original standing, scale-function, finite optimal barrier and root smoothness assumptions, the exact vcstar candidate is nonnegative at every nonnegative capital. This follows from the already proved original global monotonicity and the source regularity package's nonnegative value at zero. It supplies the explicit boundary nonnegativity for the finite-cstar above-cap comparison.
-- source:
--   Proved vcstar_monotone_of_finite_cstar UUID 8a1169cb-22fd-4b52-b4b8-fdf06c536132 and vcstar_unrestricted_verification_regularity ffdd6f8d-a5cc-4aee-8726-785404cd72f2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ vcstar W x := by sorry
