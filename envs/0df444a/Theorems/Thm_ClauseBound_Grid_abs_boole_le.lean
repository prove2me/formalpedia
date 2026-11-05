-- Prove2me | Theorems.Thm_ClauseBound_Grid_abs_boole_le
-- name    : ClauseBound.Grid.abs_boole_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:09.443909+00:00
-- url     : https://prove2.me/theorems/12dfefeb-3256-460a-8c47-205887c34ece
-- title:
--   Grid: abs boole le
-- statement:
--   An indicator is 0 or 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L37-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid

theorem ClauseBound.Grid.abs_boole_le (q : Prop) [Decidable q] : |if q then (1 : ℤ) else 0| ≤ 1 := by sorry
