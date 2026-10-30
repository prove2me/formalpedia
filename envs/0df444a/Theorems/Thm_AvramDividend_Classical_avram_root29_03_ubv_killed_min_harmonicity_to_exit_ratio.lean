-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
-- name    : AvramDividend.Classical.avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:27:04.976381+00:00
-- url     : https://prove2.me/theorems/9f4dc250-435e-48f7-ad38-0cddb0bfc911
-- title:
--   Explicit original killed-minimum scale harmonicity implies UBV corrected two-sided exit ratio
-- statement:
--   For the actual unbounded-variation spectrally negative Lévy law, positive q, 0<a, and 0<=x<=a, if the exact source finite minimum stopped discounted q-scale terminal lintegral equals ENNReal.ofReal(W x), then the original strict upward-before-ruin discounted exit expectation equals ENNReal.ofReal(W x / W a). This is a noncircular conditional adapter with the genuine killed stochastic premise explicitly supplied as hKilled, not an assertion that the premise holds. It imports only Proved a219a488, c59bf6d7 and caca9b2f.
-- source:
--   Source-faithful original stopped reward balance from Proved a219a488, then Proved unbounded corrected exit ratio c59bf6d7 and corrected expectation equivalence caca9b2f. Open be9dc931 is not imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
      ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x =
      ENNReal.ofReal (W x / W a) := by sorry
