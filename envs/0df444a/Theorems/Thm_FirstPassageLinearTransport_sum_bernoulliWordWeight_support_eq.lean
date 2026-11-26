-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_bernoulliWordWeight_support_eq
-- name    : FirstPassageLinearTransport.sum_bernoulliWordWeight_support_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:34:44.222585+00:00
-- url     : https://prove2.me/theorems/e77f4b7e-45a8-49e8-8692-b87364076b37
-- title:
--   First Passage Linear Transport: sum bernoulli Word Weight support eq
-- statement:
--   Exact tilted mass carried by Boolean words with `k` true letters.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1489-L1513
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1489-L1513

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_bernoulliWordWeight_support_eq
    (p : ℝ) (n k : ℕ) :
    ∑ v : Fin n → Bool,
        bernoulliWordWeight p v *
          (if (boolSupport v).card = k then 1 else 0) =
      tiltedBinomialMass p n k := by sorry
