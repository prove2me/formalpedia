-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_nonnegative_window_harmonicity
-- name    : AvramDividend.Classical.chat04_killed_martingale_of_nonnegative_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:48:31.037816+00:00
-- url     : https://prove2.me/theorems/0b533375-ea85-4f77-84c8-3eae2d94d3cf
-- title:
--   Killed q-scale martingale reduced to positive-reserve future-window harmonicity
-- statement:
--   For a spectrally negative Lévy process satisfying Standing and a q-scale function W, the conditional future-window q-harmonicity identity restricted to the nonnegative current reserve suffices for the killed discounted scale process to be a martingale. The proof uses the canonically covered rational-time schedule, the negative support W(y)=0 for y<0 supplied by IsScaleFunction, the proved positive-to-full conditional expectation reduction, and the proved martingale interface. The sole remaining analytic input is exactly the positive-reserve harmonicity identity.
-- source:
--   Published chat04_nat_pairing_rational_grid_coverage (34d1a207-11c0-49d1-b331-c905323990f4), chat04_future_window_harmonicity_of_nonnegative_state (a46c686a-30ac-4210-afa2-6e829a01d5b9), chat04_killed_martingale_of_future_window_harmonicity (e336ea1f-d3b9-4fbd-9a44-478efd3a0e5b), IsScaleFunction negative-support field.

import Mathlib.Data.Nat.Pairing
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_harmonicity_of_nonnegative_state
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_martingale_of_nonnegative_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hPositive : ∀ s u : ℝ≥0, s ≤ u →
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
         (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
           W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (fun ω => W (x + X.X s ω))) :
    Martingale
      (fun t ω =>
        ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) 𝓕 P := by sorry
