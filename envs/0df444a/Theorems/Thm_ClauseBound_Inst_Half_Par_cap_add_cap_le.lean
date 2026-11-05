-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Par_cap_add_cap_le
-- name    : ClauseBound.Inst.Half.Par.cap_add_cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:00.846983+00:00
-- url     : https://prove2.me/theorems/e8093761-4582-4ecf-926d-4457ddff43b5
-- title:
--   Par: cap add cap le
-- statement:
--   The two numbers of bits of a piece together are at most ⌈log₂ R^row_s⌉ + ⌈log₂ R^col_s⌉, s = i −
--   2h, h the least number ≥ 2 with p(h) ≥ 2^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L41-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L41-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par

theorem ClauseBound.Inst.Half.Par.cap_add_cap_le {c₀ lam : ℕ} (c h' i : ℕ) (hh : hOf lam ≤ c₀ * lam ^ 2) :
    (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i ≤
      Nat.clog 2 (Rrow (hOf lam) (sOf (hOf lam) i)) + Nat.clog 2 (Rcol (hOf lam) (sOf (hOf lam) i)) := by sorry
