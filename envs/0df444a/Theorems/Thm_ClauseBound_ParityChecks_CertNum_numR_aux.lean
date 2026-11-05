-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_numR_aux
-- name    : ClauseBound.ParityChecks.CertNum.numR_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:46.858795+00:00
-- url     : https://prove2.me/theorems/8b32c909-1507-4135-8b06-ca770af0a57b
-- title:
--   Cert Num: num R aux
-- statement:
--   The Cert Num construction uses the num R aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L80-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L80-L93

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

theorem ClauseBound.ParityChecks.CertNum.numR_aux {m nb r : α → ℕ} {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hL : PolyT Ls)
    (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => ((Ls x).map fun L => 2 ^ L.length * nb x ^ m x).sum + 2 ^ (cur x).length * nb x ^ e x * (nb x + 1) ^ (m x - e x) +
      (r x - 1 - (Ls x).length) * (nb x + 1) ^ m x := by sorry
