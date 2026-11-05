-- Prove2me | Theorems.Thm_ClauseBound_Boson_aFam_ok
-- name    : ClauseBound.Boson.aFam_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:15.735628+00:00
-- url     : https://prove2.me/theorems/a01afc9f-931c-4378-80be-3e3b90796b14
-- title:
--   Boson: a Fam ok
-- statement:
--   The monomials of a^μ have positive parts and weight at most |μ|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L48-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L48-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset

theorem ClauseBound.Boson.aFam_ok {μ : List ℕ} (hμ : Pos μ) : (aFam μ).Ok μ.sum := by sorry
