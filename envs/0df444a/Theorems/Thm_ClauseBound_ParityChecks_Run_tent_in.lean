-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_tent_in
-- name    : ClauseBound.ParityChecks.Run.tent_in
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:48.746655+00:00
-- url     : https://prove2.me/theorems/3dac3a74-1059-4a4d-a391-b2a113db1eba
-- title:
--   Run: tent in
-- statement:
--   The Run construction uses the tent in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L131-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L131-L158

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

theorem ClauseBound.ParityChecks.Run.tent_in {Λ : ℕ → Finset (Fin q.m)} (h : Bd q Λ) (j : ℕ) (x : Fin q.m) : Tent q (putIn j Λ x) := by sorry
