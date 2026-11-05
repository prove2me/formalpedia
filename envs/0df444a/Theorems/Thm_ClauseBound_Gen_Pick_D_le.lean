-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_D_le
-- name    : ClauseBound.Gen.Pick.D_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:19.35294+00:00
-- url     : https://prove2.me/theorems/f5049be8-7f18-4dab-8207-3272027440b1
-- title:
--   Pick: D le
-- statement:
--   D_ℓ ≤ 48·m·2^{3ℓ+x₀}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L94-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L94-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.D_le (m x₀ l : ℕ) : 3 * m * 2 ^ (l + 4) ≤ 48 * (m * 2 ^ (3 * l + x₀)) := by sorry
