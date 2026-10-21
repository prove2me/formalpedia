-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
-- name    : AvramDividend.Classical.scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T05:17:30.169445+00:00
-- url     : https://prove2.me/theorems/19cae668-ce0e-4338-8974-a5096d402877
-- title:
--   The barrier normaliser is non-zero at a finite positive optimal barrier
-- statement:
--   Let `X` be a spectrally negative Lévy process with the standing assumptions, let `q > 0` and let `W` be its `q`-scale function. Suppose the optimal barrier level `c*` is a finite strictly positive real, the scale function is strictly positive on the positive half-line, it is differentiable at every point of the positive half-line, and the exponentially tilted scale function `x ↦ e^{-φ x} W x` is monotone for some `φ > 0`. Then the barrier normaliser `divE 1 (scaleDeriv W c*)` is non-zero. This is the hypothesis `hk` of the aggregator `scaleFunction_generator_q_harmonic_of_nonzero_factor` and of each of its three branch theorems, and it is the statement that the scaled barrier value `W x / deriv W c*` is well defined below `c*`.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the value function of the barrier strategy is `v_{c*}(x) = W(x) / W'(c*)` below the barrier, which requires `W'(c*) > 0`.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : (cstar W).toReal > 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by sorry

end AvramDividend.Classical
