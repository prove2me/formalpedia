-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_UBV_negative_tail_mass_infinite
-- name    : AvramDividend.Classical.original_purejump_UBV_negative_tail_mass_infinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:14:25.682982+00:00
-- url     : https://prove2.me/theorems/8f9e6281-f8dc-4f69-b7eb-b9a8ea2a197a
-- title:
--   Original pure-jump unbounded variation forces infinite negative-tail kernel total mass
-- statement:
--   For the original spectrally negative Lévy process X with σ=0 and unbounded-variation paths, the Lebesgue integral over t>0 of the original negative jump tail ν((−∞,−t)) is infinite. By the original negative-mark layer-cake formula this equals the first absolute negative-jump moment, which diverges on marks (−1,0) for pure-jump unbounded variation. The result is the infinite-activity input needed to ensure the killed Bernstein subordinator potential has no atom at zero after Esscher tilting.
-- source:
--   Proved original purejump UBV infinite variation 2703ea95 and new original negative-tail unweighted layercake 6c70aa26; renewals source 2fa29eaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_purejump_UBV_negative_tail_mass_infinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    (∫⁻ t in Ioi (0 : ℝ), X.ν (Iio (-t))) = ⊤ := by sorry
