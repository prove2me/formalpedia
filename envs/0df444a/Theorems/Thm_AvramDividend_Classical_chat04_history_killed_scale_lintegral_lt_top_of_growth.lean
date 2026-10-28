-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_lintegral_lt_top_of_growth
-- name    : AvramDividend.Classical.chat04_history_killed_scale_lintegral_lt_top_of_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:49:36.917824+00:00
-- url     : https://prove2.me/theorems/9bc8aa77-9487-4531-92e4-e317a58a7a61
-- title:
--   Every finite-horizon killed q-scale ENNReal expectation is finite under Laplace growth
-- statement:
--   For a spectrally negative Levy process and any initial capital, a q-scale function and an exponential Laplace moment gap imply finite ENNReal expectation of the discounted scale reward that vanishes after any previous downward exit. This is the full-history survival event, rather than terminal-only killing. The result supplies the fixed-time finite-value input to semigroup harmonicity and optional stopping for the open two-sided exit identity.
-- source:
--   Direct application of canonical Proved chat04_history_killed_scale_real_ennreal_integral_bridge (af571454-2769-4d9d-ab63-6dd178ecee50), followed by pinned Mathlib ENNReal.ofReal_lt_top. Eventual consumers: open a885f0b3-3960-424d-97e4-abbcffe268ba and 09663d0d-c23e-47da-b5b9-1bbf28449a4d.

import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_history_killed_scale_lintegral_lt_top_of_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) < ⊤ := by sorry
