-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_stopped_reserve_uniform_band_bound_C2
-- name    : AvramDividend.Classical.avram_wave7_18_original_stopped_reserve_uniform_band_bound_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:47:07.753602+00:00
-- url     : https://prove2.me/theorems/8deeaa3f-0f54-4c3d-9555-7fae5c7afd01
-- title:
--   Original stopped reserve stays uniformly in its compact positive C² band before exit
-- statement:
--   For the genuine postpayment controlled spectrally-negative Lévy reserve Z_t=x+X.X t-rightLimit D t in the original filtration, with exact ContDiffOn ℝ 2 w on {y|0<y∧ENNReal.ofReal y<C}, let a right-cofinal deterministic observation grid define a strict-exterior exit stopping clock for [lower,upper], where 0<lower and every band point lies below cap C. Then the clock is an IsStoppingTime for 𝓕.rightCont. Whenever T≤clock, every s<T satisfies both explicit uniform bounds lower≤Z_s≤upper, positive below-cap membership and ContDiffWithinAt ℝ 2 w at Z_s. This combines the already Proved original countable-clock C² theorem with grid strict-exit detection and the exact clock-prefix closed-band equivalence. It makes the stopped boundedness usable by W7-08 while preserving right/left jump conventions, without asserting full UBV martingale integrability.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_stopped_reserve_uniform_band_bound_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤)) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ s : ℝ≥0, s < T →
        (lower ≤ x + X.X s ω - rightLimit D s ω ∧
          x + X.X s ω - rightLimit D s ω ≤ upper) ∧
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω) := by sorry
