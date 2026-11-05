-- Prove2me | Theorems.Thm_Eight_SecNetworks_sum_settings
-- name    : Eight.SecNetworks.sum_settings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:20:22.37429+00:00
-- url     : https://prove2.me/theorems/b684e9dc-a614-4406-9458-3837202bb524
-- title:
--   Sec Networks: sum settings
-- statement:
--   Definition 3, «A setting z_w is encoded by concatenating its K − 1 strings z_w(w')»: a sum over
--   all strings of (K − 1)λ bits of a function of the K − 1 copies is the sum over all (K − 1)-tuples of
--   strings of λ bits.
--   A tuple is a function on all K nodes with the empty string at w itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L64-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L64-L70

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

theorem Eight.SecNetworks.sum_settings {K : ℕ} (lam : ℕ) (w : Fin K) (F : (Fin K → List Bool) → ℤ) :
    ∑ z ∈ words ((K - 1) * lam), F (fun w' => if w' = w then [] else copyAt lam w w' z)
      = ∑ t ∈ tuples (fun w' => w' ≠ w) (fun _ => words lam) [], F t := by sorry
