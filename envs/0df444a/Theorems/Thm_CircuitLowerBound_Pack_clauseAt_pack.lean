-- Prove2me | Theorems.Thm_CircuitLowerBound_Pack_clauseAt_pack
-- name    : CircuitLowerBound.Pack.clauseAt_pack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:09.296392+00:00
-- url     : https://prove2.me/theorems/c6573e08-55dc-4bef-80fa-dc5f87b15e84
-- title:
--   Pack: clause At pack
-- statement:
--   The number of the clause at the place r of the table in the shift (t, q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L62-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L62-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
variable {e : MCode} {L P : ℕ}

theorem CircuitLowerBound.Pack.clauseAt_pack (e : MCode) (L P : ℕ) {r t q : ℕ} (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    clauseAt e L P ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) = (lits ((tab e).getD r zeroCl)).map (litAt e L P t q) := by sorry
