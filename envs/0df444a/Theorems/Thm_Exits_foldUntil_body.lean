-- Prove2me | Theorems.Thm_Exits_foldUntil_body
-- name    : Exits.foldUntil_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:41.819584+00:00
-- url     : https://prove2.me/theorems/dde8d23a-cfec-4949-a6df-994ad04e7a4a
-- title:
--   Exits: fold Until body
-- statement:
--   The body, run inside the loop; when it has halted, the loop goes to the next point, or halts if
--   the new accumulator passes `stop`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L47-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L47-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
set_option autoImplicit false
section
section
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}

theorem Exits.foldUntil_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldUntil start nxt M g stop c₀).Reaches S r (foldGo M (g c x b) (if stop (g c x b) then none else nxt x)) T) :
    (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by sorry
