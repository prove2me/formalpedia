-- Prove2me | Theorems.Thm_ClauseBound_Boson_Text_mem_tup
-- name    : ClauseBound.Boson.Text.mem_tup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:46.237679+00:00
-- url     : https://prove2.me/theorems/eb4df066-afba-4870-b7e0-8f2a1861f27d
-- title:
--   Text: mem tup
-- statement:
--   The Text construction uses the mem tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L83-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L83-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text

theorem ClauseBound.Boson.Text.mem_tup {M : ℕ} : ∀ {q : ℕ} {ks : List ℤ}, ks ∈ tup M q ↔ ks.length = q ∧ ∀ k ∈ ks, k ≠ 0 ∧ -(M : ℤ) ≤ k ∧ k ≤ M
  := by sorry
