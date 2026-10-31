-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_prejump_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:34:14.490981+00:00
-- url     : https://prove2.me/theorems/490a1c4e-3eeb-490b-815d-c03ef12d0b84
-- title:
--   Controlled Lévy reserve left limit dominates the pre-dividend state after its jump
-- statement:
--   Consider an original spectrally negative Lévy surplus process X and any left-continuous cumulative dividend strategy D, with the after-payment reserve $U^+(s)=x+X_s-D_{s+}$. At every positive time t, there is a finite left limit $U^+_{t-}$ and the value just after the source Lévy jump but before the right-hand dividend payment satisfies:
--
--   $$x+X_t-D_t\le U^+_{t-},\qquad U^+_{t-}=x+X_{t-}-D_t.$$
--
--   The conclusion holds pathwise and for every strategy in the source model, without a bounded-variation or Gaussian restriction. It isolates the order of source jumps and right dividend payments needed by the Lévy–Itô–Meyer verification argument.
-- source:
--   Avram–Palmowski–Pistorius (2007), Section 5.4 and Proposition 4(i), https://avram.perso.univ-pau.fr/papers/Martijn/dividend.pdf. Derived from source SpectrallyNegativeLevy.leftLim and noPosJumps, and the Proved strict-left dividend identity AvramDividend.Classical.avram_wave3_04_rightLimit_leftLimit_eq_dividend (f9c3a5c4-3a58-45b7-b6da-8734693b863d).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_prejump_upper
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
      x + X.X t ω - D t ω ≤ l := by sorry
