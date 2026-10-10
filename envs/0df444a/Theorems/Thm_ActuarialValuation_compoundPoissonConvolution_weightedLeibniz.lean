-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonConvolution_weightedLeibniz
-- name    : ActuarialValuation.compoundPoissonConvolution_weightedLeibniz
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T16:21:29.76673+00:00
-- url     : https://prove2.me/theorems/35d075ef-ec1b-44c9-89c4-84aa1af087d0
-- title:
--   Weighted finite-convolution derivative identity for compound claims
-- statement:
--   For finite convolution of discrete claim-severity coefficient sequences, weighting the coefficient at total loss s by s obeys the discrete Leibniz rule: the weight splits between the severity coefficient and the residual coefficient. This follows from j+(s-j)=s for each j≤s and finite-sum distributivity. It is an algebraic ingredient in deriving the positive-integer compound-Poisson Panjer recursion, without convergence assumptions or any unproved exchange of infinite series.
-- source:
--   Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, DOI 10.1017/S0515036100006796. The finite-convolution Leibniz statement is a derived algebraic supporting lemma, not a verbatim theorem from that paper.

import Mathlib
import Definitions.Def_actuarial_compoundPoissonConvolution

namespace ActuarialValuation

theorem compoundPoissonConvolution_weightedLeibniz
  (f g : ℕ → ℝ) (s : ℕ) :
  (s : ℝ) * compoundPoissonConvolution f g s =
    compoundPoissonConvolution (fun j => (j : ℝ) * f j) g s +
    compoundPoissonConvolution f (fun j => (j : ℝ) * g j) s := by sorry

end ActuarialValuation
