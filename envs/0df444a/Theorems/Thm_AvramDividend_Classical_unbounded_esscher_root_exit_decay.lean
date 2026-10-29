-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_exit_decay
-- name    : AvramDividend.Classical.unbounded_esscher_root_exit_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:38:11.294511+00:00
-- url     : https://prove2.me/theorems/0c9c7c97-80c0-431d-a96e-ec5a6090c1ec
-- title:
--   Exponential upper-exit scale-function comparison at a supplied positive q-root
-- statement:
--   For q>0, the canonical q-scale function W of a spectrally negative Lévy process with unbounded variation and a supplied positive root phi of ψ(phi)=q, prove W(x)≤exp(-phi(y-x)) W(y) whenever 0<x≤y. The probabilistic proof uses the two-sided exit identity for the ratio W(x)/W(y) and the exponential Lévy martingale exp(phi X_t - q t) stopped at first upper passage before ruin. This precisely isolates the stochastic first-passage inequality needed to show the positive-root Esscher tilt exp(-phi x)W(x) is monotone. All remaining analytic upper-bound steps have already been proved in separate Prove2Me results.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_root_exit_decay
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by sorry
