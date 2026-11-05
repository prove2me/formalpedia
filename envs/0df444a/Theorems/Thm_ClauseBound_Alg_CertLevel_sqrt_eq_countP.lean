-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_sqrt_eq_countP
-- name    : ClauseBound.Alg.CertLevel.sqrt_eq_countP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:02:52.105595+00:00
-- url     : https://prove2.me/theorems/9fcb8af9-ae7c-490b-84a5-144f7675f58a
-- title:
--   Cert Level: sqrt eq count P
-- statement:
--   The square root, rounded down, by counting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L279-L285
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L279-L285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.sqrt_eq_countP (n : ℕ) : Nat.sqrt n = (List.range (n + 1)).countP (fun r => decide (r * r ≤ n)) - 1 := by sorry
