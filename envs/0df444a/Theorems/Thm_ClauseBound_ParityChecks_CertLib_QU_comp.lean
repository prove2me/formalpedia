-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
-- name    : ClauseBound.ParityChecks.CertLib.QU.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:36:59.716218+00:00
-- url     : https://prove2.me/theorems/45298cbf-652f-4b45-942a-11940cc7d02d
-- title:
--   QU: comp
-- statement:
--   The property passes to a polynomial-time change of the context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L192-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L192-L193

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
attribute [local fun_prop] Groundwork.PolyT.comp


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.QU.comp {β : Type} [Enc β] {q : α → Par} (hq : QU q) {g : β → α} (hg : PolyT g) : QU fun y => q (g y) := by sorry
