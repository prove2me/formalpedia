-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
-- name    : AvramDividend.Classical.avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:58:54.172049+00:00
-- url     : https://prove2.me/theorems/a657e62e-6421-4388-bbf1-7b1fbd5ca668
-- title:
--   Bounded original-filtration exit clock gives explicit uniform reserve bound and exact C² pre-exit
-- statement:
--   For the exact original Lévy reserve Z=x+X.X-rightLimit D and source ContDiffOn ℝ 2 w on {y|0<y∧ENNReal.ofReal y<C}, define the right-cofinal countable sample first-exterior clock σ of closed positive C² band [lower,upper], and stop further at a deterministic bounded horizon B by τ=min σ B. The resulting τ is an IsStoppingTime of the original 𝓕.rightCont. Whenever T≤τ, T≤B and each s<T satisfies the quantitative stopped path bound lower≤Z_s≤upper as well as 0<Z_s, ENNReal.ofReal Z_s<C and ContDiffWithinAt ℝ 2 w in the exact source interior domain. The proof applies the already Proved original stopped reserve band/C² theorem, IsStoppingTime.min_const B and the lattice min inequalities. This supplies bounded-horizon localisation for W7-08 without claiming infinite-activity Itô integrability or simultaneous dividend right-jump dominance.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
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
        ∃ k, r k < t ∧ r k ∈ U)
    (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
      T ≤ B ∧ ∀ s : ℝ≥0, s < T →
        (lower ≤ x + X.X s ω - rightLimit D s ω ∧
          x + X.X s ω - rightLimit D s ω ≤ upper) ∧
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω) := by sorry
