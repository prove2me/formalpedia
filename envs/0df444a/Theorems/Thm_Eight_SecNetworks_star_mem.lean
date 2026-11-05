-- Prove2me | Theorems.Thm_Eight_SecNetworks_star_mem
-- name    : Eight.SecNetworks.star_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:40.282709+00:00
-- url     : https://prove2.me/theorems/c73db274-7e70-42bf-8322-234c858b7a2d
-- title:
--   Sec Networks: star mem
-- statement:
--   The strings of a choice of one string per edge on the edges at v form a (K − 1)-tuple of strings
--   of λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L76-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L76-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset

theorem Eight.SecNetworks.star_mem {K lam : ℕ} {Λ : Fin K × Fin K → List Bool}
    (hΛ : Λ ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words lam) []) (v : Fin K) :
    star Λ v ∈ tuples (fun w' => w' ≠ v) (fun _ => words lam) [] := by sorry
