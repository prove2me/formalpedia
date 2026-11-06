-- Prove2me | Theorems.Thm_Exits_foldUntil_reaches
-- name    : Exits.foldUntil_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:46.140673+00:00
-- url     : https://prove2.me/theorems/7b7e6a92-f736-4ae8-a166-a70821c5e0c8
-- title:
--   Exits: fold Until reaches
-- statement:
--   The loop from any point of the orbit and any accumulator.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L67-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L67-L99

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

theorem Exits.foldUntil_reaches {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ met (fun c x => g c x (v x)) stop c xs, size x ≤ Sx)
    (hc : ∀ l, l <+: met (fun c x => g c x (v x)) stop c xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldUntil start nxt M g stop c₀).Reaches (Sx + (Sc + Sm) + 1) ((met (fun c x => g c x (v x)) stop c xs).foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) ((met (fun c x => g c x (v x)) stop c xs).map fun x => t x + 1).sum := by sorry
