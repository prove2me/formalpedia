-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_finite_grid_pathwise_sum
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_pathwise_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:57:05.499205+00:00
-- url     : https://prove2.me/theorems/3368c582-ff0a-4100-a139-f85ee72655d8
-- title:
--   Original physical finite-band marked-jump weighted pathwise grid sum
-- statement:
--   On the genuine original Levy space, if the finite original jump-time set enumerates each intrinsic marked rectangle count, the weighted cell-count sum equals the actual weighted jump-time sum pathwise. The source enumeration premise remains explicit until P2-E supplies it.
-- source:
--   Pinned original SpectrallyNegativeLevy original X-intrinsic marked rectangles; P2-E must provide exact finite marked-jump enumeration premise hCount.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

/-- Physical jump-cell counts recover a finite original-path weighted sum. -/
theorem AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_pathwise_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a b : Fin n → ℝ≥0) (B : Fin n → Set ℝ)
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : Fin n → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a i) (b i) ×ˢ B i))
    (jumpTimes : Ω → Finset ℝ≥0)
    (cell : ℝ≥0 → Fin n)
    (hCount : ∀ ω i, (N i ω).toReal =
      (((jumpTimes ω).filter (fun u => cell u = i)).card : ℝ))
    (H : Fin n → Ω → ℝ) (ω : Ω) :
    (∑ i : Fin n, H i ω * (N i ω).toReal) =
      ∑ u ∈ jumpTimes ω, H (cell u) ω := by sorry
