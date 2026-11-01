-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_rightdrop_equals_stieltjes_atom
-- name    : AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightdrop_equals_stieltjes_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:44:17.578539+00:00
-- url     : https://prove2.me/theorems/ab6eb65a-2019-4bda-a474-f573292cb030
-- title:
--   Original reserve's exact rightward payment drop equals the Stieltjes dividend singleton mass
-- statement:
--   For any original spectrally negative Lévy source X, actual admissible strategy D, reserve x, sample ω and time t≥0, the dividend Stieltjes measure mass of the singleton {t} is precisely the ENNReal embedding of the pre-payment reserve's right-limit drop U_t−U_{t+}. This is valid at time zero and for every BV or UBV Lévy path; it couples the pathwise jump chronology to the exact stochastic discounted dividend measure, thereby offering the atomic input for a stopped Itô–Meyer verification budget. Uses the canonical dividendMeasure_singleton_eq_rightLimit_sub and independently Proved pathwise pre-payment right-limit identity, without assuming any compensated source martingale.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i) original controlled reserve jump-payment terms. Canonical Stieltjes singleton atom theorem 4f229f9a and P2 source right-limit identity 948e3f54.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightdrop_equals_stieltjes_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω {(t : ℝ)} =
      ENNReal.ofReal
        (riskProcess X x D t ω -
          Function.rightLim
            (fun s : ℝ≥0 => riskProcess X x D s ω) t) := by sorry
