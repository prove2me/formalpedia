-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_no_positive_jumps
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:39:50.800241+00:00
-- url     : https://prove2.me/theorems/51ff3291-5538-464a-bdaf-2f5215695926
-- title:
--   No upward jumps of the genuinely controlled post-payment Lévy reserve
-- statement:
--   Let X be a spectrally negative Lévy process and D a nondecreasing, left-continuous adapted dividend strategy. Define the right-continuous reserve after payments by $U^+_t=x+X_t-D_{t+}$. At every strictly positive time $t$, the càdlàg process $U^+$ has a finite left limit and does not jump upwards:
--
--   $$U^+_t\le U^+_{t-}.$$
--
--   The proof accounts for the original Lévy jump and the right-hand dividend atom at the same time. The inequality is pathwise, requires no bounded-variation restriction, and is used to orient the jump-remainder terms in the controlled Lévy Itô–Meyer formula.
-- source:
--   Avram–Palmowski–Pistorius (2007), Section 5.4 and Proposition 4(i), https://avram.perso.univ-pau.fr/papers/Martijn/dividend.pdf. Source-level consequence of spectrally negative Lévy jumps, monotone right-hand dividend payments, Proved prepayment reserve left-limit bound (490a1c4e-3eeb-490b-815d-c03ef12d0b84) and Proved dividendStrategy_le_rightLimit (953f0e91-72ae-4c9a-bc17-de52a6c87b52).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_no_positive_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ,
      Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      x + X.X t ω - rightLimit D t ω ≤ l := by sorry
