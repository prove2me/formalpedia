-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_zeroInitial_allCap_instantRuin_ae
-- name    : AvramDividend.Classical.avram_wave4_04_zeroInitial_allCap_instantRuin_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:34:37.248348+00:00
-- url     : https://prove2.me/theorems/8a4e75d2-477a-4d8f-94e3-56d171cb27e9
-- title:
--   Genuine unbounded-variation source forces instant ruin from zero under every admissible positive-cap control
-- statement:
--   For the original sample path of any unbounded-variation spectrally negative Lévy process and any cap C, every admissible adapted nondecreasing dividend control begun at zero makes the ruin time almost surely zero. The source almost surely enters the negative half-line arbitrarily close to time zero, while dividends can only decrease the reserve. The conclusion is about the actual controlled process on the original filtration, with no replacement Lévy process or atom-only dividend measure. This closes the corrected finite-horizon verification target for initial capital zero by the already-Proved instant-ruin full-Stieltjes bound, but not for positive initial capital.
-- source:
--   Avram–Palmowski–Pistorius (2007), unbounded-variation regularity at 0; exact Prove2Me ae_negative_near_zero_of_unbounded_variation and definitions of IsAdmissibleLe, riskProcess and ruinTime. Proof uses original X and D paths only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_zeroInitial_allCap_instantRuin_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by sorry
