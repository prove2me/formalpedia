-- Prove2me | Theorems.Thm_CliqueLevels_Proof_fold_le
-- name    : CliqueLevels.Proof.fold_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:43:13.840638+00:00
-- url     : https://prove2.me/theorems/a8f9f4ff-ae06-49b5-9efd-bc1ccfd5e47e
-- title:
--   Proof: fold le
-- statement:
--   On every input the second number of the state is at most b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L89-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L89-L93

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

theorem CliqueLevels.Proof.fold_le (b : ℕ) (L : List Unit) (s : Option (ℕ × ℕ)) (hs : ∀ pk, s = some pk → pk.2 ≤ b) :
    ∀ pk, L.foldl (fun s _ => roundUnder b s) s = some pk → pk.2 ≤ b := by sorry
