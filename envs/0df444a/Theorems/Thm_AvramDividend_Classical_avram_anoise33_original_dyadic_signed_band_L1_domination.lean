-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_dyadic_signed_band_L1_domination
-- name    : AvramDividend.Classical.avram_anoise33_original_dyadic_signed_band_L1_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:55:42.081582+00:00
-- url     : https://prove2.me/theorems/4da238cd-cd5f-4297-ba8b-da96d69000de
-- title:
--   Physical original finite-simple dyadic mark compensation converges with integrable bound
-- statement:
--   For every original process X with finite negative-mark intensity, cutoff n and s≤t, define the physical signed dyadic approximation M_k from the actual original jump count on cells B_n intersect (-1+i/2^k,-1+(i+1)/2^k], weighted by each cell's left endpoint, minus each cell's deterministic original Levy intensity. Then M_k is integrable, conditionally centred in the original right-continuous filtration, converges almost surely to the actual original compensated signed-band increment, and is uniformly dominated by one integrable original-space function. The conditionally centred finite-simple part uses proved 6de0a6db, while the approximation uses original negative count L2 a6562a4d and the actual signed-band integral source.
-- source:
--   Single genuinely smaller physical-source child of 936ee4d9: the dyadic marked-count approximation and its finite-activity domination. Its convergence and centring imply the parent's signed-increment conditional mean zero directly by pinned Mathlib MeasureTheory.tendsto_condExp_unique. Exact original marked source is essential; no auxiliary Brownian and no large-mark first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise33_original_dyadic_signed_band_L1_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ k, Integrable (M k) P) ∧
        (∀ k, P[M k | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
          (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω) := by sorry
