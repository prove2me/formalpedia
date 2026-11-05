-- Prove2me | Theorems.Thm_ClauseBound_Boson_Scalars_succ_mul_choose
-- name    : ClauseBound.Boson.Scalars.succ_mul_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:12.821164+00:00
-- url     : https://prove2.me/theorems/8614c573-b454-4f0b-8d18-7d47b3e4e69d
-- title:
--   Scalars: succ mul choose
-- statement:
--   (n + 1)·C(r, n + 1) = r·C(r − 1, n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Scalars.lean#L28-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Scalars.lean#L28-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Scalars
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Scalars
open Finset

theorem ClauseBound.Boson.Scalars.succ_mul_choose (r : ℤ) (n : ℕ) : ((n : ℤ) + 1) * Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by sorry
