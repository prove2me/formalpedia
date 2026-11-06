-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_partH_polyT
-- name    : ClauseBound.Inst.Half.Cert.partH_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:46.592877+00:00
-- url     : https://prove2.me/theorems/20a83104-d459-4b20-bb71-c9ef7fb5c093
-- title:
--   Cert: part H poly T
-- statement:
--   The two functions of a factorization are polynomial-time in the query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L156-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L156-L156

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.Cert.partH_polyT (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := by sorry
