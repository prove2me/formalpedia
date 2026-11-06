-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_fatou_grid_integrability_from_signed_upper
-- name    : AvramDividend.Classical.avram_p3_2_original_fatou_grid_integrability_from_signed_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:40:21.298394+00:00
-- url     : https://prove2.me/theorems/2345879f-ef37-40f7-981c-4ea7783abbf8
-- title:
--   Original physical signed-Fatou grid payoff L1 follows from positivity and integrable upper residual
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy X and admissible D, any measurable nonnegative physical-grid stopped payoff F_n bounded by w(x) plus an integrable signed original compensated source M_n+B_n is automatically integrable. This discharges the separate grid-payoff L1 premise from the canonical signed Fatou source certificate once its literal physical pathwise upper inequality and signed-source L1 have been established.
-- source:
--   Real L1 domination: 0≤F_n≤w(x)+M_n+B_n implies norm F_n≤norm(w(x)+M_n+B_n). The upper residual is integrable as the sum of a constant and the assumed actual original compensated-source signed residual. No canonical Open source, law proxy or global mesh envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_fatou_grid_integrability_from_signed_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (F M B : ℕ → Ω → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n,
      Integrable (fun ω => M n ω + B n ω) P)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω)) :
    ∀ n, Integrable (F n) P := by sorry
