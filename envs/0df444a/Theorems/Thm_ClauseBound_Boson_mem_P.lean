-- Prove2me | Theorems.Thm_ClauseBound_Boson_mem_P
-- name    : ClauseBound.Boson.mem_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:26.035938+00:00
-- url     : https://prove2.me/theorems/795c3d43-0ec0-4eee-be24-176217e6a114
-- title:
--   Boson: mem P
-- statement:
--   The Boson construction uses the mem P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L57-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L57-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic

theorem ClauseBound.Boson.mem_P {m : ℕ} {τ : Multiset ℕ} : τ ∈ P m ↔ τ.sum = m ∧ 0 ∉ τ := by sorry
