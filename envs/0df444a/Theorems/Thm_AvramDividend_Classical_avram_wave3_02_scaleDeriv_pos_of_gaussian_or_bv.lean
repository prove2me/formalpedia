-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
-- name    : AvramDividend.Classical.avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:06:39.325582+00:00
-- url     : https://prove2.me/theorems/a3226a42-404d-4ca7-9ba3-de347df56c4b
-- title:
--   Strict q-scale derivative positivity in the Gaussian and bounded-variation branches
-- statement:
--   Under the classical Standing assumptions and positive discount, the q-scale function has strictly positive ordinary derivative at every positive reserve whenever the Lévy process has a Gaussian component or bounded variation. The remaining unbounded-variation pure-jump case is deliberately excluded.
-- source:
--   Avram–Palmowski–Pistorius 2007, Proposition 1; Kuznetsov–Kyprianou–Rivero scale-function review. Canonical Proved Gaussian C1 14dc9d4c, bounded-variation C1 d42981f3, positive Esscher tilt 8d7288ac and derivative converter 396faad2. Source-faithful branch used to split canonical scaleDeriv_pos 4052a131 without claiming pure-jump regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by sorry
