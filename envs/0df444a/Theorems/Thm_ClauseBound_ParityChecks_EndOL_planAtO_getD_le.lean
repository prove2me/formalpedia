-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_EndOL_planAtO_getD_le
-- name    : ClauseBound.ParityChecks.EndOL.planAtO_getD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:27.596918+00:00
-- url     : https://prove2.me/theorems/d6116551-4b98-4be4-b5d6-af3bcdf65d7e
-- title:
--   End OL: plan At O get D le
-- statement:
--   The exponent of a plan, or else n, is at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/EndOL.lean#L34-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/EndOL.lean#L34-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_ParityChecks_EndOL
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.EndOL
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.EndOL.planAtO_getD_le {Idx : Type} [Enc Idx] (S : Solver Idx) (c n₀ k n : ℕ) (i : Idx) (s : ℕ) : (planAtO S c n₀ k n i s).getD n ≤ n := by sorry
