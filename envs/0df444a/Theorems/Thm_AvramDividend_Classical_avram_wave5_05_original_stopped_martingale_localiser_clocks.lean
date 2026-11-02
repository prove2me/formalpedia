-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_stopped_martingale_localiser_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_original_stopped_martingale_localiser_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:04:06.970194+00:00
-- url     : https://prove2.me/theorems/0df48030-cd88-4a84-a1f0-f2d1ed6e13ee
-- title:
--   Real Lévy martingale localisers cut at actual ruin are stopping, measurable, and exhaust pre-ruin time
-- statement:
--   Let S_n be any increasing family of actual stopping times for the right-continuous filtration of the same native spectrally negative Lévy process, such that S_n rises to infinity on every sample path. Then τ_n=min(S_n, ruinTime X x D) is still a true stopping time and a measurable clock, monotone in n, converging pathwise to the actual controlled ruin. The proof combines the Proved native ruin-time stopping and measurability theorems with Mathlib stopping-time minimum and lattice inf-sup interchange. This is the exact bridge from the original Avram-Palmowski-Pistorius martingale localisers T'_n to the corrected UBV core's complete Stieltjes monotone-convergence result. No finite-variation substitute or wrong-filtration law is used; this proves clock mechanics, not the unresolved stochastic local martingale identity.
-- source:
--   Avram et al. Proposition 4(i), proof equation (5.13); Proved true ruinTime stopping UUID 2d036d4f-57b5-4b28-864b-a2ff5082e323 and ruinTime measurable UUID bbfbecf4-7dfc-4812-84f3-8644c2b40b85.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_original_stopped_martingale_localiser_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSmono : ∀ ω, Monotone (fun n => S n ω))
    (hSsup : ∀ ω, (⨆ n, S n ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ n : ℕ, Measurable
      (fun ω => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ ω, Monotone (fun n => min (ruinTime X x D ω) (S n ω))) ∧
    (∀ ω, (⨆ n, min (ruinTime X x D ω) (S n ω)) =
      ruinTime X x D ω) := by
  sorry
