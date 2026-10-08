-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:43:13.878708+00:00
-- url     : https://prove2.me/theorems/59531c77-8eaf-44ac-a657-5b3ae9dcf8d6
-- title:
--   Strict positivity of the canonical q-scale function under Avram's standing assumptions
-- statement:
--   For every spectrally negative Lévy process satisfying the paper's exact standing assumptions, every positive discount rate and positive capital level have a strictly positive q-scale function. This separates the analytic positivity conjunct from the independent strong-Markov/dividend-value factorisation. The Gaussian branch has a separately proved conditional reduction, while the zero-Gaussian infinite-variation and positive-drift branches require the Lévy-exponent divergence argument.
-- source:
--   Avram, Palmowski and Pistorius (2007) §3 on positivity of the q-scale function, combined with the platform's exact IsScaleFunction and Standing predicates, the proved scaleFunction_strict_pos_of_eventual_psi_bound, ψ quadratic upper bound, and positive-Gaussian branch. The missing non-Gaussian eventual ψ growth is the explicit pending obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaleFunction_strict_pos_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a) :
    0 < W a := by sorry
