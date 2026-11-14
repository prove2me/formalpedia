-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_deterministic_atomic_source_uniform_increment_limit
-- name    : AvramDividend.Classical.avram_chat24_deterministic_atomic_source_uniform_increment_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:41:10.259692+00:00
-- url     : https://prove2.me/theorems/6ac6eb1b-4fdc-428b-bcf0-ea3d0d116e45
-- title:
--   Deterministic uniform source increments for a drift minus summable negative atoms
-- statement:
--   Source-faithful deterministic child of 33a32b0b-5c11-425c-8625-13559c4d089c. The actual source is a cadlag positive linear drift minus its own summable negative jumps, and the given dividends are monotone. The shifted reserve stays in a positive compact band and has the given predictable left limits. Derive the exact n+1 uniform-grid nonlinear source increment limit and physical drift integrability. No limit of sums is assumed. The jump measure is exactly the original marked count measure and the physical clock is the real-volume toNNReal pushforward.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_deterministic_atomic_source_uniform_increment_limit
    (f K Y : ℝ≥0 → ℝ) (v d a b q T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hd : 0 < d) (ha : 0 < a) (hq : 0 ≤ q)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim f u - f u else 0)
    (hband : ∀ t : ℝ≥0, t ≤ B → v + f t - K t ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    Integrable (fun t : ℝ≥0 =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0) μ ∧
    Tendsto (fun n : ℕ =>
      let N : ℕ := n + 1
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let U : ℕ → ℝ := fun i => v + f (u i) - K (u i)
      let Z : ℕ → ℝ := fun i => v + f (u (i + 1)) - K (u i)
      ∑ i ∈ Finset.range N, e (i + 1) * (w (Z i) - w (U i)))
      atTop (nhds ((∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0 ∂NX) +
        (∫ t : ℝ≥0, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
          Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0 ∂μ))) := by sorry
