-- Prove2me | Theorems.Thm_ClauseBound_Both_End_bound_mono
-- name    : ClauseBound.Both.End.bound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:45:33.520167+00:00
-- url     : https://prove2.me/theorems/cbdd2222-31cd-46cb-8f02-180efad8a54a
-- title:
--   End: bound mono
-- statement:
--   The bound in m grows with the constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/End.lean#L24-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/End.lean#L24-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_Both_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Both ClauseBound.Both.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

theorem ClauseBound.Both.End.bound_mono {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k m : ℕ) (hr : 0 ≤ r m) : SatM.bound r D k m ≤ SatM.bound r D' k m := by sorry
