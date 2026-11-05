-- Prove2me | Theorems.Thm_Eight_Width_splitAll_map
-- name    : Eight.Width.splitAll_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:01:42.690416+00:00
-- url     : https://prove2.me/theorems/7d2156a3-2738-48d8-b731-f202c4d0a3ac
-- title:
--   Width: split All map
-- statement:
--   Renaming the variables commutes with `splitAll`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L132-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L132-L137

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

theorem Eight.Width.splitAll_map {V W : Type} (f : V → W) : ∀ (φ : List (List (V × Bool))) (ys : List V),
    (splitAll ys φ).map (fun D => D.map fun l => (f l.1, l.2)) = splitAll (ys.map f) (φ.map fun D => D.map fun l => (f l.1, l.2))
  := by sorry
