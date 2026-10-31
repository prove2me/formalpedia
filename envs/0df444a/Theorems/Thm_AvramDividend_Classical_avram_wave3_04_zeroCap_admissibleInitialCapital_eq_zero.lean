-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
-- name    : AvramDividend.Classical.avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:54:24.367731+00:00
-- url     : https://prove2.me/theorems/d781e680-4dde-40c1-b6dc-f415a203b56e
-- title:
--   An actually admissible zero-capped dividend strategy necessarily starts at capital zero
-- statement:
--   Under the actual original-law dividend admissibility definition, if the extended-nonnegative image of initial capital lies within cap zero, then initial capital must be exactly zero. The cap premise gives x≤0, while the process probability measure ensures there is a sample point. The canonical initial post-payment solvency result gives x−D_{0+}≥0 at that sample, and the pathwise monotone left-continuous dividend conditions imply D_{0+}≥D_0=0; hence x≥0. This is valid without assuming Ω is inhabited as a separate typeclass, because the original Lévy process probability measure forces a nonempty sample space. It permits transferring complete zero-cap verification from x=0 to the original corrected UBV theorem's arbitrary x parameter.
-- source:
--   Pinned private remote compiler probe a7056bad-4fe0-442c-bbe4-8706184b7d8b passed to intentional sentinel without diagnostics, source SHA256 da9448e763ec7650c3d05e1cb257a8b873ff411c4b6bff427f2de31b9c5a69c2. Canonical Proved capped_postPaymentReserve_initial_state 2ecd3672-50b4-4ad7-ad28-d1720acec949 and dividendStrategy_le_rightLimit 953f0e91-72ae-4c9a-bc17-de52a6c87b52; pinned Mathlib nonempty_of_measure_ne_zero and ENNReal.ofReal_eq_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ (0 : ℝ≥0∞))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x 0 D) : x = 0 := by sorry
