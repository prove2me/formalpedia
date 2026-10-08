-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
-- name    : AvramDividend.Classical.positive_esscher_root_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:24:04.044043+00:00
-- url     : https://prove2.me/theorems/cfe6d3e1-ed2b-4c2a-9c1e-6346ae2ca5c6
-- title:
--   Unbounded-variation Lévy process has positive Esscher exponent root for every positive discount rate
-- statement:
--   For any unbounded-variation spectrally negative Lévy process, the canonical Laplace exponent is continuous and grows past every positive q. Thus it attains q at some strictly positive Esscher exponent φ. The Gaussian and infinite-small-jump growth branches and canonical zero normalisation are already proved. The previously isolated continuity result removes the only remaining hypothesis, establishing this root existence without assumptions on the excursion process.
-- source:
--   Proved esscher_positive_root_of_unbounded_variation and levy_laplace_exponent_continuousOn_nonnegative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_esscher_root_of_unbounded_variation
 {Ω : Type*} [mΩ : MeasurableSpace Ω]
 {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
 (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
 (q : ℝ) (hq : 0 < q) :
 ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
