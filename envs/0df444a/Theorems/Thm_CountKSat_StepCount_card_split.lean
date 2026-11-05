-- Prove2me | Theorems.Thm_CountKSat_StepCount_card_split
-- name    : CountKSat.StepCount.card_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:37.85779+00:00
-- url     : https://prove2.me/theorems/ed95ba8f-3d26-410a-970c-cd1a5d46eb0b
-- title:
--   Step Count: card split
-- statement:
--   If L means «P and Q» and R means «P and not Q», then the number of a with P a is the sum of the
--   numbers for L and for R.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L78-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L78-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Definitions.Def_CountKSat_StepCount
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.StepCount

theorem CountKSat.StepCount.card_split {ι : Type} [Fintype ι] (P Q L R : ι → Prop) [DecidablePred P] [DecidablePred L] [DecidablePred R]
    (hL : ∀ a, L a ↔ P a ∧ Q a) (hR : ∀ a, R a ↔ P a ∧ ¬ Q a) :
    (univ.filter P).card = (univ.filter L).card + (univ.filter R).card := by sorry
