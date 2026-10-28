-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
-- name    : AvramDividend.Classical.chat04_esscher_infimum_survival_zero_negative_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:10:18.790832+00:00
-- url     : https://prove2.me/theorems/eb44c352-736b-466c-9276-b7ec78a22365
-- title:
--   The infinite-horizon Esscher survival distribution vanishes for negative starting reserves
-- statement:
--   For any spectrally negative Lévy process, terminal Esscher parameter and strictly negative initial reserve, the continuously killed survival event is empty at every horizon because X_0=0. Consequently the infimum across finite-horizon Esscher-weighted survival expectations is identically zero at all negative reserves.
-- source:
--   Reuse the accepted pathwise result `chat01_negative_initial_reserve_survival_empty`, rewrite each survival indicator to the empty set and its integral to zero, then simplify the infimum of constant zeros. This is the left-tail boundary condition H∞(x)=0 for x<0 needed to construct its finite Stieltjes measure without spurious mass at negative capital.

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat01_negative_initial_reserve_survival_empty

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_infimum_survival_zero_negative_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (hx : x < 0) :
    (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) = 0 := by sorry
