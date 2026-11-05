-- Prove2me | Theorems.Thm_ClauseBound_Boson_Dual_pow_mul_factorial_dvd
-- name    : ClauseBound.Boson.Dual.pow_mul_factorial_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:59.00288+00:00
-- url     : https://prove2.me/theorems/957b32bc-a592-4f70-af60-6bce241f680a
-- title:
--   Dual: pow mul factorial dvd
-- statement:
--   k^m·m! divides (m·k)!.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L108-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L108-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset

theorem ClauseBound.Boson.Dual.pow_mul_factorial_dvd {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : k ^ m * m.factorial ∣ (m * k).factorial := by sorry
