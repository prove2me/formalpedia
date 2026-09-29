-- Prove2me | Theorems.Thm_Erdos146_exponentGain_pos
-- name    : Erdos146.exponentGain_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:43:29.294639+00:00
-- url     : https://prove2.me/theorems/aa3485b5-6833-4f98-8b1c-44c1a36d34ea
-- title:
--   The exponent gain is positive
-- statement:
--   Verification that the parameters of Section 6 exist. The construction needs a Hamming radius $\tau \in (0, 1/2)$ and a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$, where $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$; the source verifies at the end of Section 6 that such parameters exist. The gain $\varepsilon$ over the conjectured exponent $3/2$ is strictly positive. This is the whole point: the excess is polynomial, not merely a constant.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11557-L11560

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.exponentGain_pos : 0 < exponentGain := by sorry
