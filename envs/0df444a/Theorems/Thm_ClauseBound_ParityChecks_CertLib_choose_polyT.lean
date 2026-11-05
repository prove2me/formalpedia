-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_choose_polyT
-- name    : ClauseBound.ParityChecks.CertLib.choose_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:51:41.191034+00:00
-- url     : https://prove2.me/theorems/16f0bb4e-d1e3-4459-b776-25f51e6b5b93
-- title:
--   Cert Lib: choose poly T
-- statement:
--   The binomial coefficient C(n, k) is polynomial-time, for k in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L137-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L137-L138

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

theorem ClauseBound.ParityChecks.CertLib.choose_polyT {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).choose (k x) := by sorry
