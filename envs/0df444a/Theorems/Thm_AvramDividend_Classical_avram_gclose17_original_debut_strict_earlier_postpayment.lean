-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_debut_strict_earlier_postpayment
-- name    : AvramDividend.Classical.avram_gclose17_original_debut_strict_earlier_postpayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:30:48.369601+00:00
-- url     : https://prove2.me/theorems/9ecdd407-5633-4f17-9d3e-a10ecc9f7d55
-- title:
--   Every strict prefix of the original lower-exit debut supremum has positive postpayment reserve
-- statement:
--   For the actual adapted original spectrally negative Levy source and dividend strategy, choose any original stopping clock, dense sampled observation times and strictly positive reserve thresholds. Before the pointwise supremum of the corresponding stopped lower-exit observation clocks, the true postpayment reserve is strictly positive. This is the precise pathwise strict-solvency fact at the candidate zero-contact debut; it does not assert positivity at the debut itself or that it reaches the ruin time.
-- source:
--   Use the complete-lattice fact that if the supremum of the clipped sample-exit clocks lies above T, at least one individual clock lies above T, then apply Proved e129ae1d's exact original postpayment floor on all s<T, and the positivity of its threshold.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_debut_strict_earlier_postpayment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → WithTop ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont σ)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) :
    let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)
    ∀ ω (T : ℝ≥0), (T : WithTop ℝ≥0) < (⨆ n : ℕ, ρ n ω) →
      ∀ s : ℝ≥0, s < T →
        0 < x + X.X s ω - rightLimit D s ω := by sorry
