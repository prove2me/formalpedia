-- Prove2me | Theorems.Thm_Erdos146_manuscriptHammingRadius_le
-- name    : Erdos146.manuscriptHammingRadius_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:52:40.183826+00:00
-- url     : https://prove2.me/theorems/df86bc60-248e-44bc-93d7-e55bd262269d
-- title:
--   The manuscript Hamming radius is admissible
-- statement:
--   Verification that the parameters of Section 6 exist. The construction needs a Hamming radius $\tau \in (0, 1/2)$ and a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$, where $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$; the source verifies at the end of Section 6 that such parameters exist. The explicit numerical radius fixed by the manuscript satisfies the required bound.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17597-L17602

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.Archimedean

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.manuscriptHammingRadius_le (dimension : ℕ) :
    (manuscriptHammingRadius dimension : ℝ) ≤
      tau * (dimension : ℝ) := by sorry
