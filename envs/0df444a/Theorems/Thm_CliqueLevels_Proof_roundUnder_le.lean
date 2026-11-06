-- Prove2me | Theorems.Thm_CliqueLevels_Proof_roundUnder_le
-- name    : CliqueLevels.Proof.roundUnder_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:41.475525+00:00
-- url     : https://prove2.me/theorems/3f02cc1b-d840-4010-b941-a895c4551a28
-- title:
--   Proof: round Under le
-- statement:
--   After a round the second number is at most b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L76-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L76-L86

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

theorem CliqueLevels.Proof.roundUnder_le {b : ℕ} {s : Option (ℕ × ℕ)} {pk : ℕ × ℕ} (h : roundUnder b s = some pk) : pk.2 ≤ b := by sorry
