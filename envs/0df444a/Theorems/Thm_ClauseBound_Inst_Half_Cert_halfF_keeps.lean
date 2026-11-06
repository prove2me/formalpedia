-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_halfF_keeps
-- name    : ClauseBound.Inst.Half.Cert.halfF_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:35.146808+00:00
-- url     : https://prove2.me/theorems/dd0a0ef3-503a-4b09-adbc-2511f2550b9c
-- title:
--   Cert: half F keeps
-- statement:
--   The pieces with ρ = 1/√2 keep polynomial time, for all values of the two parameters.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L159-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L159-L160

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

theorem ClauseBound.Inst.Half.Cert.halfF_keeps (c₀ c : ℕ) : (halfF c₀ c).Keeps := by sorry
