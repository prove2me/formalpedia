-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_rest_le
-- name    : ClauseBound.Gen.Rate.rest_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:38.574503+00:00
-- url     : https://prove2.me/theorems/10218c83-7902-42d7-9a5e-3bb1e773cd0d
-- title:
--   Rate: rest le
-- statement:
--   What is added to z + size cnt at one level, apart from a doubling, is at most X^(c+3).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L140-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L140-L178

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

theorem ClauseBound.Gen.Rate.rest_le (g c lam B bits sd R sp : ℕ) (hc : 1 ≤ c) (hlam : 1 ≤ lam) (hg : 6 ≤ g) (hbits : bits ≤ (2 * lam) ^ c)
    (hsd : sd ≤ (2 * lam) ^ c) (hR : R ≤ g ^ 4) (hsp : sp ≤ R * (2 * lam) ^ c + 1) :
    R * sd + (g * g) ^ 2 * lam + g ^ 2 * (g * B + g ^ 2 * bits + 1) + 2 + 2 * sp ≤ (g ^ 2 * (lam + B)) ^ (c + 3) := by sorry
