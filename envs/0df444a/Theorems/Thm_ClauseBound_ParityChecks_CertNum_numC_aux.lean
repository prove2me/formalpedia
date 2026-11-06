-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_numC_aux
-- name    : ClauseBound.ParityChecks.CertNum.numC_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:45.521686+00:00
-- url     : https://prove2.me/theorems/0a3e9579-885d-4ca1-81e3-c53702e00309
-- title:
--   Cert Num: num C aux
-- statement:
--   The Cert Num construction uses the num C aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L102-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L102-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertNum.numC_aux {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : PolyT e) :
    PolyT fun a => ((List.range (m a)).map fun x =>
      2 ^ Par.colOf (Ls a) (cur a) x * nb a ^ ((Ls a).length + if x < e a then 1 else 0) *
        (nb a + 1) ^ (r a - ((Ls a).length + if x < e a then 1 else 0))).sum := by sorry
