-- Prove2me | Theorems.Thm_CliqueLevels_Proof_len_roundUnder_le
-- name    : CliqueLevels.Proof.len_roundUnder_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:43:46.85628+00:00
-- url     : https://prove2.me/theorems/dd247e71-d918-47fd-a47b-49e360440524
-- title:
--   Proof: len round Under le
-- statement:
--   A round makes the word of the state longer by at most 3b + 16.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L98-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L98-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed

theorem CliqueLevels.Proof.len_roundUnder_le (b : ℕ) (s : Option (ℕ × ℕ)) : len (roundUnder b s) ≤ len s + (3 * b + 16) := by sorry
