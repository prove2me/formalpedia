-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:04:51.983707+00:00
-- url     : https://prove2.me/theorems/cde0be7e-3751-4e81-ae63-7566e86cb8e9
-- title:
--   Public original all-cap source-frozen Stieltjes dividend cell nonpositivity
-- statement:
--   Public source-exact bridge for original controlled spectrally negative Lévy X and original admissible right-payment D. Every pre-ruin half-open physical cell has full Stieltjes dividend measure mass plus the after-source before/right-payment cap-linear reserve difference nonpositive, including singular continuous variation, right endpoint atom, zero and cap contact, and finite/infinite cap. Only public Proved secant, original rightLimit monotonicity and interval-measure identity are used.
-- source:
--   Reconstruct the 333d39f4 proven original source-frozen interval calculation from public Proved dependencies a4675c8a (cap global secant), f7eef805 (rightLimit monotonicity), and f9211de0 (Ioc mass). Public target avoids the protected private-import boundary for canonical P3 integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry
