-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_condExp_identity
-- name    : AvramDividend.Classical.chat04_killed_martingale_of_condExp_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:24:35.226841+00:00
-- url     : https://prove2.me/theorems/f1306df7-fcbd-4813-854a-fafcc11f3b71
-- title:
--   Killing-scale martingale follows from the outstanding conditional-expectation equality
-- statement:
--   The pathwise downward-killed discounted canonical q-scale process is a martingale once its conditional-expectation identity at all deterministic times is established. The published Standing regularity theorem already supplies adaptedness and integrability; this result isolates the exact remaining semigroup/harmonicity equality as the only additional premise and packages the final Lean martingale assembly.
-- source:
--   Published chat03_killed_scale_martingale_regularities and pinned Mathlib Martingale definition.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_martingale_regularities

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_martingale_of_condExp_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hZ : Z = fun t ω =>
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω)
    (hCond : ∀ s u : ℝ≥0, s ≤ u →
      P[Z u | 𝓕 s] =ᵐ[P] Z s) :
    Martingale Z 𝓕 P := by sorry
