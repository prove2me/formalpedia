-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_Dset_succ
-- name    : ClauseBound.ParityChecks.Run.Dset_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:30.760384+00:00
-- url     : https://prove2.me/theorems/7183c593-23f3-471a-a837-0c5309a3ed2c
-- title:
--   Run: Dset succ
-- statement:
--   The Run construction uses the Dset succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L80-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L80-L83

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

theorem ClauseBound.ParityChecks.Run.Dset_succ {e : ℕ} (he : e < q.m) : Dset q.m (e + 1) = (Dset q.m e).erase ⟨e, he⟩ := by sorry
