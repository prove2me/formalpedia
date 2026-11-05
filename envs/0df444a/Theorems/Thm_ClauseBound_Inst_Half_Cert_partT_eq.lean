-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_partT_eq
-- name    : ClauseBound.Inst.Half.Cert.partT_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:40.664388+00:00
-- url     : https://prove2.me/theorems/29e99e45-8e21-48ee-957e-84444f42ea80
-- title:
--   Cert: part T eq
-- statement:
--   The number j of a pair may be cut off at 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L100-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L100-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.Cert.partT_eq (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b θ : List Bool) :
    partT pad tr top h s T a b θ = ((labs T tr h s)[ofWord θ]?).elim 0 fun p => bodyT pad tr top h s T a b (min p.1 (2 * h)) p.2 := by sorry
