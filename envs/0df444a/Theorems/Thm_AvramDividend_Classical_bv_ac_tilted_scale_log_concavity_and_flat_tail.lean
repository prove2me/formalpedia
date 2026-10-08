-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_scale_log_concavity_and_flat_tail
-- name    : AvramDividend.Classical.bv_ac_tilted_scale_log_concavity_and_flat_tail
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T10:54:01.183717+00:00
-- url     : https://prove2.me/theorems/5c7bc166-d63a-469f-924b-033359c79de6
-- title:
--   Log-concavity and vanishing logarithmic slope of tilted BV scale function
-- statement:
--   For the standing BV absolutely continuous spectrally negative Lévy process at positive Cramér–Esscher root φ, log of the tilted scale V(x)=exp(-φx)W^(q)(x) is concave on (0,infinity), and its ordinary derivative tends to zero at infinity. This isolates two nonlinear fluctuation-theory properties. First-order smoothness is handled separately by the existing Prove2Me theorem scaleFunction_contDiff_one_of_absolutely_continuous_levy, and measure reconstruction, derivatives and tail nonnegativity by already-Proved reusable lemmas. This theorem is mathematically deep and remains Open until a genuine excursion or renewal proof is supplied.
-- source:
--   Chan–Kyprianou–Savov (2011), bounded-variation excursion derivative; Kuznetsov–Kyprianou–Rivero (2012), logarithmic excursion tail under Esscher tilt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_tilted_scale_log_concavity_and_flat_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, V x = Real.exp (-(φ * x)) * W x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) ∧
      Tendsto (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
        atTop (𝓝 (0 : ℝ)) := by sorry
