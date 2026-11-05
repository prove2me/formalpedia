-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_num_congr
-- name    : ClauseBound.ParityChecks.Run.num_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:50.326201+00:00
-- url     : https://prove2.me/theorems/19b784ea-321c-4f3a-afc0-a3310134e30a
-- title:
--   Run: num congr
-- statement:
--   The numerator uses the B_i with i ≤ i₀ only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L206-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L206-L212

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}

theorem ClauseBound.ParityChecks.Run.num_congr (A : ℤ) {B B' : ℕ → ℤ} (h : ∀ i ≤ q.i₀, B i = B' i) (Ls : List Chk) (cur : Chk) (e : ℕ) : q.num A B Ls cur e = q.num A B' Ls cur e := by sorry
