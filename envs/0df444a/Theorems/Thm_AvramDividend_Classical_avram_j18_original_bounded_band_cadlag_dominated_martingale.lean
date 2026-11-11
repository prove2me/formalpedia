-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_cadlag_dominated_martingale
-- name    : AvramDividend.Classical.avram_j18_original_bounded_band_cadlag_dominated_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:19:26.69217+00:00
-- url     : https://prove2.me/theorems/096ba1c2-3532-46fe-b10f-3e3f162b31a1
-- title:
--   Original compensated bounded small-band field is càdlàg and horizon-dominated
-- statement:
--   Construct the actual original-compensated bounded-jump field with simultaneous cutoff convergence, deterministic-time original-filtration L1 martingale law, right-continuous sample paths, zero initial value, and one integrable bound on each fixed original clock horizon. Finite-activity original jump count integrability and gap arguments justify the source bound.
-- source:
--   Source-faithful analytic and regularity child of Open 61f39bfe. Strictly stronger than deterministic-time core, adds exactly what bounded optional sampling needs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_j18_original_bounded_band_cadlag_dominated_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ, ∃ B : Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) ∧
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖Jsmall t ω‖ ≤ B ω) := by sorry
