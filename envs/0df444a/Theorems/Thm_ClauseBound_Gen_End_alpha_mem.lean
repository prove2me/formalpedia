-- Prove2me | Theorems.Thm_ClauseBound_Gen_End_alpha_mem
-- name    : ClauseBound.Gen.End.alpha_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:12:38.501613+00:00
-- url     : https://prove2.me/theorems/b8ed4465-8782-422e-94df-bf706565cc9d
-- title:
--   End: alpha mem
-- statement:
--   0 ≤ log₂(1/ρ) ≤ 1 for 1/2 ≤ ρ < 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L72-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L72-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End

theorem ClauseBound.Gen.End.alpha_mem {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ Real.logb 2 (1 / ρ) ∧ Real.logb 2 (1 / ρ) ≤ 1 := by sorry
