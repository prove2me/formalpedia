-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_emod_eq
-- name    : ClauseBound.ParityChecks.emod_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:20.761257+00:00
-- url     : https://prove2.me/theorems/de282d5b-bff8-4589-b9d9-35a4a08ae7d8
-- title:
--   Parity Checks: emod eq
-- statement:
--   A number in [0, 2^n] is the remainder modulo 2^{n+1} of any number congruent to it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Congr.lean#L43-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Congr.lean#L43-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Congr
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Congr
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)

theorem ClauseBound.ParityChecks.emod_eq {n : ℕ} {a b : ℤ} (h0 : 0 ≤ a) (ha : a ≤ 2 ^ n) (hab : b ≡ a [ZMOD 2 ^ (n + 1)]) : b % 2 ^ (n + 1) = a := by sorry
