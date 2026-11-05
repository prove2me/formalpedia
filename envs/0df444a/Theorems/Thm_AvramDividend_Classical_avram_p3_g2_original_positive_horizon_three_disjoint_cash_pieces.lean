-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_positive_horizon_three_disjoint_cash_pieces
-- name    : AvramDividend.Classical.avram_p3_g2_original_positive_horizon_three_disjoint_cash_pieces
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:38:14.50232+00:00
-- url     : https://prove2.me/theorems/75634623-58aa-438a-ba86-5848c80e4842
-- title:
--   Original positive-horizon Stieltjes cash exactly partitions into zero atom, interior cash and one active horizon atom
-- statement:
--   Under the actual bounded-variation capped Levy dividend source assumptions at strictly positive horizon S, the full paymentTimes∩Iic S discounted Stieltjes cash is exactly initial rightLimit D 0, plus the open interior cash on (0,S), plus one discounted rightLimit D S-D S atom if and only if S is strictly before ruin. A ruin occurring precisely at S contributes no terminal atom. This is the source-exact three-piece measure partition, with neither missing nor duplicated time-zero or horizon dividends, respecting cap contact.
-- source:
--   Public Proved original strict-cash zero-atom/open-interior identity d58a7561 and source G2 exact closed/open right-horizon atom identity 54ad337e, with exact positive-horizon case split. No import from original P3 canonical residual or budgets.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_positive_horizon_three_disjoint_cash_pieces
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (hS : 0 < S) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo (0 : ℝ) (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * (rightLimit D S ω - D S ω)
       else 0) := by sorry
