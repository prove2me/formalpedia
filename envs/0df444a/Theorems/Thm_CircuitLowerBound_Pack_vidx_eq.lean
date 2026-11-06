-- Prove2me | Theorems.Thm_CircuitLowerBound_Pack_vidx_eq
-- name    : CircuitLowerBound.Pack.vidx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:42:52.337973+00:00
-- url     : https://prove2.me/theorems/2f9a202e-c399-4e72-aa69-392dffde77d0
-- title:
--   Pack: vidx eq
-- statement:
--   The number of a variable of the table, without reductions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L48-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Pack.lean#L48-L59

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

theorem CircuitLowerBound.Pack.vidx_eq (hg : GoodCode e) (hF : Fits e L P) {c : TCl} (hc : c ∈ tab e) {l : TLit} (hl : l ∈ lits c) {t q : ℕ} (ht : t < 2 ^ bt e L)
    (hq : q < 2 ^ bq e L) :
    vidx e L P t q l = (l.1 * 2 ^ (bt e L + 1) + tval (bt e L) t l.2.1) * 2 ^ (bq e L + 1) + (qval P q l.2.2.1 + l.2.2.2.1) ∧
      tval (bt e L) t l.2.1 < 2 ^ (bt e L + 1) ∧ qval P q l.2.2.1 + l.2.2.2.1 < 2 ^ (bq e L + 1) := by sorry
