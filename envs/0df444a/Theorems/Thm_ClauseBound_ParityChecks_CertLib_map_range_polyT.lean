-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_map_range_polyT
-- name    : ClauseBound.ParityChecks.CertLib.map_range_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:47.64114+00:00
-- url     : https://prove2.me/theorems/17c2e10a-8f95-4397-8818-7926ac02502d
-- title:
--   Cert Lib: map range poly T
-- statement:
--   A list of values at i < n is polynomial-time, for n in unary; the values are only needed for
--   indices given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L115-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L115-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.map_range_polyT {β : Type} [Enc β] {n : α → ℕ} {f : α → ℕ → β} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).map (f x) := by sorry
