-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_first_le
-- name    : ClauseBound.Gen.Rate.size_first_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:08.092195+00:00
-- url     : https://prove2.me/theorems/cdf6ce89-e7e2-4b7c-a1f3-c2a44e2b58bd
-- title:
--   Rate: size first le
-- statement:
--   The bit length of the first budget, with the parts that depend on cnt and z split off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L87-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L87-L110

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

theorem ClauseBound.Gen.Rate.size_first_le (Kup lam B cnt z : ℕ) :
    size (cnt * PaddedDescent.F.instLen Kup lam B + 8 * z + 4 * lam + 40) ≤
      size cnt + size z + (Kup - 1) * lam + size (4 * lam + Kup * (3 * B + 14) + 10) + size (4 * lam + 40) + 4 := by sorry
