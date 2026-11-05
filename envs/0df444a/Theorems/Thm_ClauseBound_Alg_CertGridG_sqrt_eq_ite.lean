-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_eq_ite
-- name    : ClauseBound.Alg.CertGridG.sqrt_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:16.737979+00:00
-- url     : https://prove2.me/theorems/c2adfe5c-4971-4801-aec2-aa12055b18de
-- title:
--   Cert Grid G: sqrt eq ite
-- statement:
--   The square root of m from that of m / 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L167-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L167-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.CertGridG.sqrt_eq_ite (m : ℕ) :
    Nat.sqrt m = if (2 * Nat.sqrt (m / 4) + 1) * (2 * Nat.sqrt (m / 4) + 1) ≤ m then 2 * Nat.sqrt (m / 4) + 1 else 2 * Nat.sqrt (m / 4) := by sorry
