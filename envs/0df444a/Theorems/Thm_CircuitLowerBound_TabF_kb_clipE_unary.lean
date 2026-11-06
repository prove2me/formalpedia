-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_kb_clipE_unary
-- name    : CircuitLowerBound.TabF.kb_clipE_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:04:37.032223+00:00
-- url     : https://prove2.me/theorems/bfeb9564-6317-4b86-ac9a-380eefa9094a
-- title:
--   Tab F: kb clip E unary
-- statement:
--   The first number of a table that is cut off at a number in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L48-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L48-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

theorem CircuitLowerBound.TabF.kb_clipE_unary {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => kb (clipE (e x) (L x)) := by sorry
