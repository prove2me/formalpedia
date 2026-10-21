-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_ratio_bound_tilted_monotone
-- name    : AvramDividend.Classical.gaussian_ratio_bound_tilted_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:25:51.239832+00:00
-- url     : https://prove2.me/theorems/b0982df4-490e-4150-84c2-cc84275093ca
-- title:
--   Positive Gaussian Esscher root and first-passage scale ratio imply tilted monotonicity
-- statement:
--   If a spectrally negative Lévy process has a nonzero Gaussian coefficient and q>0, its positive Esscher root φ exists. Suppose a strictly positive scale function satisfies the exponential first-passage ratio inequality W(x)/W(y)≤exp(-φ(y-x)) whenever 0<x≤y and ψ(φ)=q. Then the Esscher-normalised factor exp(-φx)W(x) is nondecreasing on positive x. The proof uses positivity to multiply the ratio inequality by W(y) and the independently proved decay-to-monotonicity theorem. The ratio bound itself remains a substantive first-passage hypothesis.
-- source:
--   Proved positive_esscher_root_of_gaussian and exit_decay_implies_tilted_monotone.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_ratio_bound_tilted_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hratio : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-φ * (y - x))) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
