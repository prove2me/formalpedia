-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_GW_polyT
-- name    : ClauseBound.ParityChecks.CertOL.GW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:20.952614+00:00
-- url     : https://prove2.me/theorems/757aa699-70c7-428f-ab69-f1020391c320
-- title:
--   Cert OL: GW poly T
-- statement:
--   The weight of a profile is polynomial-time, for the number of layers and the numbers of marks in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L57-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L57-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertOL.GW_polyT {R : α → ℕ} {ws : α → List ℤ} {lo hi : α → List ℕ} {t : α → ℕ → ℕ} (hR : Unary R) (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi)
    (ht : Unary fun p : α × ℕ => t p.1 p.2) : PolyT fun x => GW (R x) (ws x) (lo x) (hi x) (t x) := by sorry
