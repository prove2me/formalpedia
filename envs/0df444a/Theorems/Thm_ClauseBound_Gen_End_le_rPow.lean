-- Prove2me | Theorems.Thm_ClauseBound_Gen_End_le_rPow
-- name    : ClauseBound.Gen.End.le_rPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:39:36.186137+00:00
-- url     : https://prove2.me/theorems/7aa332aa-d86f-4f8f-909d-92205548ea59
-- title:
--   End: le r Pow
-- statement:
--   1/(c·(log₂(m+2))^c) ≤ 1/(log₂(m+2))^α for 0 ≤ α ≤ 1 ≤ c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L86-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L86-L94

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

theorem ClauseBound.Gen.End.le_rPow {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 1 ≤ c) (m : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ SatM.rPow α m := by sorry
