-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_entropy_add_logLikelihood_le_zero
-- name    : FirstPassageLinearTransport.entropy_add_logLikelihood_le_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:31:22.551776+00:00
-- url     : https://prove2.me/theorems/95be1690-e3c2-452d-b134-8497a5123c4c
-- title:
--   First Passage Linear Transport: entropy add log Likelihood le zero
-- statement:
--   Gibbs' inequality for a Bernoulli law, in exactly the logarithmic form
--   needed to cancel the entropy exponential in the Stirling estimate.  Keeping
--   this lemma elementary avoids importing a measure-theoretic relative-entropy
--   interface into the finite-word cone.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L497-L531
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L497-L531

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.entropy_add_logLikelihood_le_zero
    {p u : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (hu₀ : 0 < u) (hu₁ : u < 1) :
    Real.binEntropy u + u * Real.log p +
        (1 - u) * Real.log (1 - p) ≤ 0 := by sorry
