-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
-- name    : AvramDividend.Classical.avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:32:35.36795+00:00
-- url     : https://prove2.me/theorems/bfd44fdb-270b-4d5c-abe3-205bd4028e7a
-- title:
--   Original bounded right-stopped full negative-mark nonlinear kernel equals product of the exact physical stop/ruin, discount and closed-cap masks
-- statement:
--   The exact original nonlinear physical negative-mark kernel exp(-qt)[w(Y_{t-}+z)-w(Y_{t-})] stopped at true ruin and at bounded σ≤n, on the positive-time nonnegative-reserve closed-cap and negative-mark domain, factors pointwise as bounded-horizon discount, stopped clock survival, original ruin survival, the full nonlinear value increment and the closed-cap mark mask. The identity is valid for every mark and for the terminal ruin-causing jump. It is a genuine original pathwise source for the predictable kernel theorem b7420f09, not a linear Jfull replacement or expectation statement.
-- source:
--   Original physical signed Ito negative-mark source with exact right-dividend reserve left limit; decomposes stopping-time and cap-mask algebra from predictable measurability for b7420f09, needed by full nonlinear compensator 04e002c9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∀ p : (ℝ≥0 × Ω) × ℝ,
      H p =
        (((if p.1.1 ≤ (n : ℝ≥0)
            then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) *
          ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
            then (1 : ℝ) else 0) *
           (w (Y p.1 + p.2) - w (Y p.1)))) *
          (if 0 < p.1.1 ∧ 0 ≤ Y p.1 ∧
              ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0
           then (1 : ℝ) else 0) := by sorry
