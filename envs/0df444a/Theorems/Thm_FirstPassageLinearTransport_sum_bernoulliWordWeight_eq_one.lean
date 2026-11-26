-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_bernoulliWordWeight_eq_one
-- name    : FirstPassageLinearTransport.sum_bernoulliWordWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:34:19.463449+00:00
-- url     : https://prove2.me/theorems/eeed8164-428b-559e-bc43-15ac5c0f945b
-- title:
--   First Passage Linear Transport: sum bernoulli Word Weight eq one
-- statement:
--   Bernoulli word weights have total mass one, proved on the finite word
--   tree rather than through a measure-theoretic product-space interface.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1430-L1445
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1430-L1445

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_bernoulliWordWeight_eq_one (p : ℝ) :
    ∀ r : ℕ, ∑ v : Fin r → Bool, bernoulliWordWeight p v = 1 := by sorry
