-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_ediv_natCast
-- name    : ClauseBound.Alg.CertLevel.ediv_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:01:06.342221+00:00
-- url     : https://prove2.me/theorems/7b562a5b-a92d-4799-855f-e98591ccc4d9
-- title:
--   Cert Level: ediv nat Cast
-- statement:
--   The quotient, rounded down, in terms of quotients of natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L42-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L42-L52

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

theorem ClauseBound.Alg.CertLevel.ediv_natCast (a : ℤ) (b : ℕ) :
    a / (b : ℤ) = if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else if b = 0 then 0 else -(((a.natAbs - 1) / b + 1 : ℕ) : ℤ) := by sorry
