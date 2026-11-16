-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:57:23.133577+00:00
-- url     : https://prove2.me/theorems/0ed9f6b1-f4a9-4979-8406-33747c34617f
-- title:
--   Original physical negative-Borel void deficit squeezed between first and second factorial moments
-- statement:
--   For the actual marked negative-Borel jumps on the original Lévy process and original P, set rate = T ν(B), and q_n=P(at least one B-jump by T/n). For large n, rate - rate²/(2n) ≤ n q_n ≤ rate. The upper bound uses first moment E[N_h]=ν(B)h; the lower bound uses E[N_h(N_h−1)]=ν(B)²h² and pointwise 1_{N>0} ≥ N−N(N−1)/2. The source first and second factorial moments are already Proved; the remaining issue is transferring the count/void event and Bochner integrals to the exact point-process expression. This is the missing stochastic input for the original exact Poisson void probability 786aeafb.
-- source:
--   Proved source first count moment 4faa7c77, source second factorial moment 6d1258a3, finite source physical count realization 84a4791e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let rate : ℝ := (T : ℝ) * (X.ν B).toReal
    let q : ℕ → ℝ := fun n =>
      1 - (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal
    ∀ᶠ n in (Filter.atTop : Filter ℕ),
      rate - (rate ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)) ≤
          ((n : ℕ) : ℝ) * q n ∧
        ((n : ℕ) : ℝ) * q n ≤ rate := by sorry
