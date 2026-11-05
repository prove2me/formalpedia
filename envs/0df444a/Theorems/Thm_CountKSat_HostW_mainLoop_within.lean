-- Prove2me | Theorems.Thm_CountKSat_HostW_mainLoop_within
-- name    : CountKSat.HostW.mainLoop_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:38.453974+00:00
-- url     : https://prove2.me/theorems/9d16cdb1-9da3-4913-b3af-d7f32888c32d
-- title:
--   Host W: main Loop within
-- statement:
--   The loop, from a state that reaches the result w within t steps: at most t rounds. The last
--   state s' is left on the main stack, and on it what
--   the head leaves of the word of its output `some w`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L178-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L178-L199

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_Groundwork_Host_mainLoop_within

set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing
variable {M : Stepped (List Bool) (List Bool)}
variable [Enc M.σ]
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
include hS hO

theorem CountKSat.HostW.mainLoop_within (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {w : List Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S w s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ M.out s' = some w ∧
      Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
        (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [] (st (wd w ++ (.L :: .R :: .R :: (wd s' ++ []))) [] [] [])) := by sorry
