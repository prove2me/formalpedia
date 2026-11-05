-- Prove2me | Theorems.Thm_Eight_Width_toN_widthReduce
-- name    : Eight.Width.toN_widthReduce
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:56:13.798197+00:00
-- url     : https://prove2.me/theorems/58e31f05-7400-47d9-a642-ca5eb73e8f07
-- title:
--   Width: to N width Reduce
-- statement:
--   `widthReduce φ`, with its variables read as numbers, is what the program returns on φ with its
--   variables read as numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L144-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L144-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat

theorem Eight.Width.toN_widthReduce {n : ℕ} (φ : Sat3.CNF n) : Decode.toN (widthReduce φ) = splitN n (Decode.toN φ) := by sorry
