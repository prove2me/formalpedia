-- Prove2me | Theorems.Thm_Erdos146_entropyUpperEndpoint_lt_one
-- name    : Erdos146.entropyUpperEndpoint_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:42:51.682513+00:00
-- url     : https://prove2.me/theorems/9c8f4d0a-9d47-4d60-8e95-603ba76535ae
-- title:
--   The upper endpoint of the entropy window is below one
-- statement:
--   Verification that the parameters of Section 6 exist. The construction needs a Hamming radius $\tau \in (0, 1/2)$ and a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$, where $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$; the source verifies at the end of Section 6 that such parameters exist. The upper endpoint $C(\tau)$ of the admissible window for $\beta$ is less than $1$, so the retention probability $p = 2^{-\beta m}$ is genuinely subcritical.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11538-L11540

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.entropyUpperEndpoint_lt_one : entropyUpperEndpoint < 1 := by sorry
