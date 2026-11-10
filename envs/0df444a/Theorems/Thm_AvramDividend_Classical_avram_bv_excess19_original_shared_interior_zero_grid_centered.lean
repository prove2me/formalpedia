-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess19_original_shared_interior_zero_grid_centered
-- name    : AvramDividend.Classical.avram_bv_excess19_original_shared_interior_zero_grid_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T20:13:03.30346+00:00
-- url     : https://prove2.me/theorems/318810ed-2a34-48f5-b5db-2ec008827e4a
-- title:
--   Shared original BV interior and zero-contact finite-grid compensated martingale is L1 and centred
-- statement:
--   For an actual original-process physical grid, the same finite-row compensated source combines the strictly positive-reserve intrinsic marked-jump martingale with a survival-masked, zero-prepayment-reserve compensated negative-jump count. Finite negative Levy activity and original right-continuous predictability give integrability and exactly zero expectation of the combined source. Unlike separate compartmental martingales, this establishes one shared stopped M that the physical cash and terminal error ledger must use, with no arbitrary-grid convergence or global B L1 assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_triangular_grid_compensator_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess19_original_shared_interior_zero_grid_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (hDstrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n i, u n i ≤ u n (i + 1))
    (r : (n : ℕ) → Fin (n + 1) → ℕ → ℝ≥0)
    (hsr : ∀ n (i : Fin (n + 1)) k, u n i.val < r n i k)
    (hrt : ∀ n (i : Fin (n + 1)) k, r n i k ≤ u n (i.val + 1))
    (hShort : ∀ n (i : Fin (n + 1)),
      Tendsto (fun k => r n i k - u n i.val) atTop (𝓝 0))
    (hLong : ∀ n (i : Fin (n + 1)),
      Tendsto (fun k => u n (i.val + 1) - r n i k)
        atTop (𝓝 (u n (i.val + 1) - u n i.val)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (v : (n : ℕ) → Fin (n + 1) → ℝ) :
    let Mpos : ℕ → Ω → ℝ := fun n ω =>
      let K : ℝ≥0 → Ω → ℝ := fun S ω' =>
        let τ : Ω → ℝ≥0 := fun ξ =>
          (min (ruinTime X x D ξ) (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2)
              p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if p.1 ∈ E ∧ p.2 < 0 then
            Real.exp (-(q * (p.1.1 : ℝ))) *
              (w (Function.leftLim
                (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
                  p.1.1 + p.2) -
               w (Function.leftLim
                (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
                  p.1.1))
          else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ξ =>
          ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ξ -
              Function.leftLim (fun z : ℝ≥0 => X.X z ξ) t ≠ 0}).map
            (fun t : ℝ≥0 => (t,
              X.X t ξ - Function.leftLim (fun z : ℝ≥0 => X.X z ξ) t)))
        (∫ p, H ((p.1, ω'), p.2) ∂(NX ω')) -
          (∫ t, ∫ z, H ((t, ω'), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map
              Real.toNNReal))
      Finset.sum (Finset.range (n + 1))
        (fun i => K (u n (i + 1)) ω - K (u n i) ω)
    let Mzero : ℕ → Ω → ℝ := fun n ω =>
      Finset.sum Finset.univ (fun i : Fin (n + 1) =>
        (if (u n i.val : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
                (u n i.val) = 0 then v n i else 0) *
        ((((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) t)))
          (Ioc (u n i.val) (u n (i.val + 1)) ×ˢ Iio (0 : ℝ))).toReal -
          (((u n (i.val + 1) - u n i.val : ℝ≥0) : ℝ≥0∞) *
            X.ν (Iio (0 : ℝ))).toReal))
    ∀ n, Integrable (fun ω => Mpos n ω + Mzero n ω) P ∧
      (∫ ω, Mpos n ω + Mzero n ω ∂P) = 0 := by sorry
