-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_cap_unary
-- name    : ClauseBound.Alg.CertLevel.cap_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:01:08.537206+00:00
-- url     : https://prove2.me/theorems/281414e8-48e4-4b13-ab63-dc6d9a386e15
-- title:
--   Cert Level: cap unary
-- statement:
--   The number of bits through which a piece factors is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L99-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L99-L101

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
variable (hP : P.Keeps)
include hP

theorem ClauseBound.Alg.CertLevel.cap_unary {tr : α → Bool} {s : α → Step} {l : α → U} {i : α → ℕ} (ht : PolyT tr) (hs : PolyT s) (hl : PolyT l) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (s x).h (l x).length (i x) := by sorry
