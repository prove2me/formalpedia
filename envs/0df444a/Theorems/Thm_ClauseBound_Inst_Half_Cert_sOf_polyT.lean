-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_sOf_polyT
-- name    : ClauseBound.Inst.Half.Cert.sOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:09.437569+00:00
-- url     : https://prove2.me/theorems/550c11cc-eaaf-4893-8f88-3a2930c974a7
-- title:
--   Cert: s Of poly T
-- statement:
--   The number s of a piece is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L51-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L51-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_sOf_polyT

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.Cert.sOf_polyT {h i : α → ℕ} (hh : PolyT h) (hi : PolyT i) : PolyT fun x => sOf (h x) (i x) := by sorry
