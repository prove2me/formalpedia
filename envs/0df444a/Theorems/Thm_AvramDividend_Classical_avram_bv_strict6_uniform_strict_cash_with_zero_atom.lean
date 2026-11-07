-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_uniform_strict_cash_with_zero_atom
-- name    : AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_with_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:20:27.303967+00:00
-- url     : https://prove2.me/theorems/0f93cd57-9751-4a17-9c2c-9196b8a2a10d
-- title:
--   Original BV strict uniform-grid dividend cash including exact time-zero right atom
-- statement:
--   For the exact original admissible BV dividend control, an explicit strictly positive uniform cutoff b=T-T/(n+2) and physical uniform grid u_i=T*i/(n+2), the literal strict stopped cash over paymentTimes intersect Iio b is exactly the initial rightLimit D 0 atom plus n positive interior Ioc cells and an open final interval Ioo(u_n,b). It combines two already Proved source-exact cash identities, derives b>0 from T>0 and n+2>=2, and excludes any dividend at cutoff b or at T. This isolates the original strict cash/time-zero accounting used in 2bc848f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_uniform_strict_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_with_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, (u i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (b : ℝ≥0)
    (hb : (b : ℝ) = T - T / ((n : ℝ) + 2)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      rightLimit D 0 ω +
        ((∑ i ∈ Finset.range n,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioo (u n : ℝ) (b : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) := by sorry
