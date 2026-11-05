-- Prove2me | Theorems.Thm_Eight_Width_splitClause_map
-- name    : Eight.Width.splitClause_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:01:54.137674+00:00
-- url     : https://prove2.me/theorems/d6c2e7e3-5c88-4644-a8bc-7212ad635067
-- title:
--   Width: split Clause map
-- statement:
--   Renaming the variables commutes with `splitClause`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L120-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L120-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat

theorem Eight.Width.splitClause_map {V W : Type} (f : V → W) : ∀ (ys : List V) (C : List (V × Bool)),
    (splitClause ys C).map (fun D => D.map fun l => (f l.1, l.2)) = splitClause (ys.map f) (C.map fun l => (f l.1, l.2))
  := by sorry
