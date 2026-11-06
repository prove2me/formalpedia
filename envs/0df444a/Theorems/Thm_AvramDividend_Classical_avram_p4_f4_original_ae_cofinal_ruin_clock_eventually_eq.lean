-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
-- name    : AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:52:37.956078+00:00
-- url     : https://prove2.me/theorems/2589726d-57da-4f58-a45d-1ad5539e266f
-- title:
--   Original clipped ruin clock equals its natural clock eventually under almost-sure cofinal spatial localisation
-- statement:
--   For the unchanged original spectrally negative Levy process and actual ruinTime X x D, monotonically increasing spatial stopped clocks S_k with almost-sure supremum top ensure the clipped original tau_k=min(min(ruin,n),S_k) is literally equal eventually to natural tau=min(ruin,n) on a full-probability set. This weakens everywhere-cofinality of the earlier exact F4 clock theorem, permitting the genuine exceptional null paths inherent in stochastic localisation.
-- source:
--   Apply exact real/extended original ruin stopped clock definitions and lt_iSup_iff pointwise on the full-probability cofinal event. No stochastic martingale assumptions, terminal continuity or cash-limit assumptions are introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τk k ω = τ ω := by sorry
