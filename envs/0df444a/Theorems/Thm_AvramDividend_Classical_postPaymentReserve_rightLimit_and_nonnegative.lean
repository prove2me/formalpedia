-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative
-- name    : AvramDividend.Classical.postPaymentReserve_rightLimit_and_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:40:46.758314+00:00
-- url     : https://prove2.me/theorems/ee511693-82ae-4510-948d-f5277173e5d3
-- title:
--   The book-value reserve tends rightward to the post-payment reserve, preserving solvency
-- statement:
--   For a spectrally negative Lévy path X and a monotone left-continuous dividend path D, the book-value reserve U_s=x+X_s−D_s converges as s↓t to the post-payment reserve U_t+=x+X_t−D_{t+}. Therefore if U_s≥0 eventually for strict-right s near t, then U_t+≥0 as a closed-order limit. The second implication is the exact pathwise boundary fact needed to turn strict pre-ruin solvency into nonnegative after-payment terminal residuals; it does not assert the unjustified stochastic stopped HJB budget or assume nonnegative reserves at ruin itself.
-- source:
--   Use X.rightCont restricted to Ioi t and pinned Mathlib Monotone.tendsto_rightLim and rightLim_eq_sInf; closed Ici preserves nonnegative limit. All original hypotheses are explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_rightLimit_and_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω) (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) ∧
    ((∀ᶠ s in 𝓝[>] t, 0 ≤ riskProcess X x D s ω) →
      0 ≤ x + X.X t ω - rightLimit D t ω) := by sorry
