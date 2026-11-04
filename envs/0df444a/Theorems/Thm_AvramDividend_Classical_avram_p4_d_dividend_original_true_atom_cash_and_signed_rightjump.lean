-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_atom_cash_and_signed_rightjump
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_atom_cash_and_signed_rightjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:55:08.796378+00:00
-- url     : https://prove2.me/theorems/091382d2-c04d-449d-8b15-f0fa5a42ba9c
-- title:
--   Original payment singleton cash and correctly ordered right-jump signed correction agree and are nonpositive
-- statement:
--   At any eligible original source stopping time t≤T, the exact original Stieltjes singleton mass paid through paymentTimes(ruinTime) has the same real value as discounted physical right-dividend payment. The dividendStrategy_le_rightLimit source theorem supplies increment nonnegativity without a new hypothesis. Alongside the source post-X/pre-D payment secant assumption hjump, the actual simultaneous source/right-dividend signed correction exp(-qt)*(δ+w(Uafter)-w(Ubefore)) is nonpositive. Includes time zero and surviving horizon atoms, and retains original positive-ruin exclusion through paymentTimes.
-- source:
--   Avram–Palmowski–Pistorius Prop 4(i), Eq 5.13; source d19177af, proved dividendStrategy_le_rightLimit 953f0e91, source proved P4-D exact sign 9f4070e7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_atom_cash_and_signed_rightjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    (ω : Ω) (T t : ℝ≥0) (ht : t ≤ T)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ((μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal =
      if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
        else 0) ∧
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
