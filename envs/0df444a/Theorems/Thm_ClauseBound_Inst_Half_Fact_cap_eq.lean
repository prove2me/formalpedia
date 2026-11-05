-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Fact_cap_eq
-- name    : ClauseBound.Inst.Half.Fact.cap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:49.923221+00:00
-- url     : https://prove2.me/theorems/dd20e1c3-cebb-430f-b85c-af0c119eb800
-- title:
--   Fact: cap eq
-- statement:
--   The number of bits of the labels: nothing is cut off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L39-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L39-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact
import Theorems.Thm_PaddedDescent_F_cap_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact

theorem ClauseBound.Inst.Half.Fact.cap_eq {c₀ c lam : ℕ} (hC : Cst c₀ c lam) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) :
    (halfF c₀ c).cap tr h' lam i = Nat.clog 2 (bif tr then ClauseBound.Part.Rcol (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)
      else ClauseBound.Part.Rrow (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)) := by sorry
