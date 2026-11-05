-- Prove2me | Theorems.Thm_CircuitLowerBound_Pack_pack_lt
-- name    : CircuitLowerBound.Pack.pack_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:07.810199+00:00
-- url     : https://prove2.me/theorems/f528d970-1a88-48aa-9562-68070499946a
-- title:
--   Pack: pack lt
-- statement:
--   The Pack construction uses the pack lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L76-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L76-L80

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

theorem CircuitLowerBound.Pack.pack_lt {e : MCode} {L r t q : ℕ} (hr : r < 2 ^ rb e) (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    (r * 2 ^ bt e L + t) * 2 ^ bq e L + q < 2 ^ nb e L := by sorry
