-- Prove2me | Theorems.Thm_ClauseBound_Boson_Final_factorsThrough_mono
-- name    : ClauseBound.Boson.Final.factorsThrough_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:24:58.489139+00:00
-- url     : https://prove2.me/theorems/52eccb38-651b-4453-bab5-2537528cb6cf
-- title:
--   Final: factors Through mono
-- statement:
--   A factorization with values below b is one with values below any b' ≥ b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L30-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L30-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final

theorem ClauseBound.Boson.Final.factorsThrough_mono {X X' : Type} {F : X → X' → ℤ} {c : ℕ} {b b' : ℤ} (h : Pieces.FactorsThrough F c b) (hb : b ≤ b') :
    Pieces.FactorsThrough F c b' := by sorry
