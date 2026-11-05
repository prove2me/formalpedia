-- Prove2me | Theorems.Thm_CliqueLevels_Proof_fold_eq
-- name    : CliqueLevels.Proof.fold_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:42:32.209334+00:00
-- url     : https://prove2.me/theorems/c6b6e7a8-5c77-4859-8f41-efc63ded783c
-- title:
--   Proof: fold eq
-- statement:
--   The state after ℓ rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L52-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L52-L73

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

theorem CliqueLevels.Proof.fold_eq (x₀ b l : ℕ) : (unary l).foldl (fun s _ => roundUnder b s) (if 2 ^ x₀ ≤ b then some (2 ^ x₀, 2 ^ x₀) else none) =
    if Levels.Gen.K x₀ l ≤ b then some (2 ^ (3 * l + x₀), Levels.Gen.K x₀ l) else none := by sorry
