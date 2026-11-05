-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_prod_range_polyT
-- name    : ClauseBound.ParityChecks.CertLib.prod_range_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:43.213985+00:00
-- url     : https://prove2.me/theorems/de20cb6b-1154-4fca-897c-89777b5669cf
-- title:
--   Cert Lib: prod range poly T
-- statement:
--   A product of integers over i < n is polynomial-time, for n in unary; the factors are only needed
--   for indices given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L107-L111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.prod_range_polyT {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => ∏ i ∈ Finset.range (n x), f x i := by sorry
