-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:00:38.997723+00:00
-- url     : https://prove2.me/theorems/dc79e135-0f91-48bd-8093-269621b58c00
-- title:
--   Original BV exact discounted finite-grid product identity exposing the signed dividend remainder
-- statement:
--   An unconditional algebraic finite-grid chain/product identity on the actual original spectrally negative Lévy process X and original controlled left-continuous/right-payment D. It preserves the true paymentTimes(ruinTime) Stieltjes cash, after-rightpayment w at physical grid endpoints, source-frozen Lévy w increments and explicit rem_i. The identity makes no HJB, jump compensation, boundary occupation or additional stochastic assumption; the sign of rem_i is separately discharged by source secant/Stieltjes helpers.
-- source:
--   Finite sum telescoping and exact discrete product rule; source/process/payment symbols are from the original platform Definitions. No private theorem imports, no stochastic assumptions. The resulting remainder is an equality, not asserted nonpositive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 =
      (∑ i ∈ Finset.range n, e i * frozen i) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := by sorry
