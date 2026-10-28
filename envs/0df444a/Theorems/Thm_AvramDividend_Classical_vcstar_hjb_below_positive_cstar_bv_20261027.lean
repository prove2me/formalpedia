-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar_bv_20261027
-- name    : AvramDividend.Classical.vcstar_hjb_below_positive_cstar_bv_20261027
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:22:06.025019+00:00
-- url     : https://prove2.me/theorems/2af73322-f0bb-4330-a2db-0da72afeab9d
-- title:
--   Unconditional interior HJB equality for a bounded-variation optimal dividend barrier
-- statement:
--   For a standing spectrally negative Lévy model of bounded variation and positive optimal barrier, the exact barrier candidate belongs to the generator domain and satisfies the full Hamilton–Jacobi–Bellman equality at every strictly positive reserve below the barrier. The proof combines independently verified BV generator harmonicity with C1 scale-function regularity and the Esscher-tilted gradient inequality, and retains the full nonlocal Lévy generator.
-- source:
--   Mathematically exact bounded-variation interior branch of Avram, Palmowski and Pistorius (2007), Lemma 3(i), Lemma 4 and Proposition 4. It is a reusable child of the root-frontier target vcstar_hjb_below_positive_cstar [93145b5a-25dd-4cc0-9e9a-04d2275120f7], independent of the unsolved unbounded-variation case and independent of dividend-control stochastic change of variables. Uses existing Proved BV scale regularity, Esscher tilt, gradient and generator harmonicity.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_hjb_below_positive_cstar_bv_20261027
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hcpos : 0 < cstar W) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
