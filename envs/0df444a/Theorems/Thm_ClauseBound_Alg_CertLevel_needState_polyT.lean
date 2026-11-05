-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needState_polyT
-- name    : ClauseBound.Alg.CertLevel.needState_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:18:58.920937+00:00
-- url     : https://prove2.me/theorems/2ecc9f8a-b21f-4ab8-ba19-3d91fed6e1f6
-- title:
--   Cert Level: need State poly T
-- statement:
--   The exponent for the state of the descent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L375-L377
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L375-L377

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.needState_polyT {cnt z B lam Kst inst : α → ℕ} (h1 : PolyT cnt) (h2 : PolyT z) (h3 : PolyT B) (h4 : PolyT lam) (h5 : PolyT Kst) (h6 : PolyT inst) :
    PolyT fun x => max (Nat.size (cnt x * inst x + 8 * z x + 4 * lam x + 40)) (max (lam x) (max (Nat.size (B x)) (Nat.size (Kst x)))) := by sorry
