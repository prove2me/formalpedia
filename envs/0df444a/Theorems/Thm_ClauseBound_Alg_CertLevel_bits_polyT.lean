-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_bits_polyT
-- name    : ClauseBound.Alg.CertLevel.bits_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:29:38.579383+00:00
-- url     : https://prove2.me/theorems/b1f9c4fe-0fa4-4a72-bc99-7e600564b59d
-- title:
--   Cert Level: bits poly T
-- statement:
--   The bound for the number of bits of the values of the pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L335-L336
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L335-L336

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.bits_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => P.bits (s x).h (l x).length := by sorry
