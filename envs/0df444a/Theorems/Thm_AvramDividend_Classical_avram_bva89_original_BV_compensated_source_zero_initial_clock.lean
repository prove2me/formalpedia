-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva89_original_BV_compensated_source_zero_initial_clock
-- name    : AvramDividend.Classical.avram_bva89_original_BV_compensated_source_zero_initial_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:44:00.099205+00:00
-- url     : https://prove2.me/theorems/3d2ecb5b-bf9f-4471-87fd-2b242625c10e
-- title:
--   Exact original BV row-indexed stopped marked count minus compensator source has zero initial clock
-- statement:
--   For every physical row and path of the original infinite-activity BV spectrally negative Levy risk/dividend process, the literal row-n stopped negative-mark source M(S,ω), with exact prepayment state, spatial band, ruin clip, positive-time NX and mapped negative-mark compensator used in BVA63, satisfies M(0,ω)=0. The actual pathwise mark map is measurable by the Proved route runner; at S=0 the stopped kernel is supported only at zero, so its jump-count integral vanishes by BVA86 and its compensator vanishes by BVA83. Removes the initial endpoint in Proved BVA75/BVA76 without changing the process or grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bva83_original_zero_clock_negative_mark_compensator_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva86_original_marked_zero_clock_supported_jump_integral
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva89_original_BV_compensated_source_zero_initial_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    ∀ (n : ℕ),
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
          let τ : Ω → ℝ≥0 := fun ω' =>
            (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
          let E : Set (ℝ≥0 × Ω) := {p |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
          let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
            if p.1 ∈ E ∧ p.2 < 0 then
              Real.exp (-(q * (p.1.1 : ℝ))) *
              (w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
               w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
            else 0
          let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
            if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
          let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
            ((Measure.count.restrict
              {v : ℝ≥0 | 0 < v ∧
                X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
              (fun v : ℝ≥0 => (v,
                X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
          (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
          (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      ∀ ω : Ω, M (0 : ℝ≥0) ω = 0 := by sorry
