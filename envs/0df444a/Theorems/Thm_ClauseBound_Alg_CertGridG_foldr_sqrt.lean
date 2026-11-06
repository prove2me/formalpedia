-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_foldr_sqrt
-- name    : ClauseBound.Alg.CertGridG.foldr_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:31.80738+00:00
-- url     : https://prove2.me/theorems/2b3abe2d-4539-4773-a1a6-56dab2e2ed65
-- title:
--   Cert Grid G: foldr sqrt
-- statement:
--   The square root, two binary digits of the number at a time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L181-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L181-L188

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

theorem ClauseBound.Alg.CertGridG.foldr_sqrt (n : ℕ) : ∀ k j : ℕ, n / 4 ^ (j + k) = 0 →
    (List.range' j k).foldr (fun i r => if (2 * r + 1) * (2 * r + 1) ≤ n / 4 ^ i then 2 * r + 1 else 2 * r) 0 = Nat.sqrt (n / 4 ^ j) := by sorry
