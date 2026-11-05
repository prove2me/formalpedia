-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_mem_Dset
-- name    : ClauseBound.ParityChecks.Run.mem_Dset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:41.999074+00:00
-- url     : https://prove2.me/theorems/53a902da-949d-48e8-bab4-3d42f8e436a6
-- title:
--   Run: mem Dset
-- statement:
--   The Run construction uses the mem Dset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L77-L78

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

theorem ClauseBound.ParityChecks.Run.mem_Dset {e : ℕ} (he : e < q.m) : (⟨e, he⟩ : Fin q.m) ∈ Dset q.m e := by sorry
