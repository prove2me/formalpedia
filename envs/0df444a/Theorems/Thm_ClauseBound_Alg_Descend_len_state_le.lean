-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_len_state_le
-- name    : ClauseBound.Alg.Descend.len_state_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:41.98809+00:00
-- url     : https://prove2.me/theorems/f75978db-3513-41a7-8b0b-e678a3a35670
-- title:
--   Descend: len state le
-- statement:
--   The word of a state with at most cnt well-formed instances, and a sum and a factor below 2^z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L68-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L68-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

theorem ClauseBound.Alg.Descend.len_state_le (st : DState) {K lam B cnt z : ℕ} (hl : st.2.1.length = lam) (hc : st.2.2.length ≤ cnt)
    (hw : ∀ I ∈ st.2.2, WFe K lam B I) (hs : st.1.1.natAbs < 2 ^ z) (hf : st.1.2 < 2 ^ z) :
    len st ≤ cnt * instLen K lam B + 8 * z + 4 * lam + 40 := by sorry
