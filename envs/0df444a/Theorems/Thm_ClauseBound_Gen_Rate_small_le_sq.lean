-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_small_le_sq
-- name    : ClauseBound.Gen.Rate.small_le_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:55.58308+00:00
-- url     : https://prove2.me/theorems/1ec10eee-9e40-4557-bbf8-136449e63ca6
-- title:
--   Rate: small le sq
-- statement:
--   The two small numbers of the first budget are below X², X = K·(λ + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L113-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L113-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)

theorem ClauseBound.Gen.Rate.small_le_sq (Kup lam B : ℕ) (hK : 44 ≤ Kup) (hlam : 1 ≤ lam) :
    4 * lam + Kup * (3 * B + 14) + 10 ≤ (Kup * (lam + B)) ^ 2 ∧ 4 * lam + 40 ≤ (Kup * (lam + B)) ^ 2 := by sorry
