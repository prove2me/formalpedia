-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_numO_polyT
-- name    : ClauseBound.ParityChecks.CertNum.numO_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:03.739951+00:00
-- url     : https://prove2.me/theorems/eda9964d-2c6d-4cfe-b513-cc5959da7298
-- title:
--   Cert Num: num O poly T
-- statement:
--   The numerator with A and the B_i taken as the representatives modulo 2^β (`bal`) of the values
--   of the given functions `orcA` and `orcB` is polynomial-time, for e in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L170-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L170-L179

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertNum.numO_polyT {q : α → Par} (hq : QU q) {orcA : α → List Chk → ℤ} {orcB : α → List Chk → Chk → ℕ → ℕ → ℤ} {Ls : α → List Chk} {cur : α → Chk}
    {e : α → ℕ} (hA : PolyT fun p : α × List Chk => orcA p.1 p.2)
    (hB : PolyT fun p : α × List Chk × Chk × ℕ × ℕ => orcB p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).numO (orcA x) (orcB x) (Ls x) (cur x) (e x) := by sorry
