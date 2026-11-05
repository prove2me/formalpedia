-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_encF_polyT
-- name    : ClauseBound.Inst.Half.Cert.encF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:37.36836+00:00
-- url     : https://prove2.me/theorems/00f10759-3a21-4f45-935c-f15831a90d07
-- title:
--   Cert: enc F poly T
-- statement:
--   The partition that a string stands for is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L76-L77

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

theorem ClauseBound.Inst.Half.Cert.encF_polyT {T : α → PT} {h : α → ℕ} {a : α → List Bool} (hT : PolyT T) (hh : PolyT h) (ha : PolyT a) : PolyT fun x => encF (T x) (h x) (a x) := by sorry
