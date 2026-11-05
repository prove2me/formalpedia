-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_lam_putIn
-- name    : ClauseBound.ParityChecks.Run.lam_putIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:49.371628+00:00
-- url     : https://prove2.me/theorems/b08dc08c-ecc0-442a-9540-d2c27c832f1d
-- title:
--   Run: lam put In
-- statement:
--   The Run construction uses the lam put In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L97-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L97-L106

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

theorem ClauseBound.ParityChecks.Run.lam_putIn (Ls : List Chk) (cur : Chk) {e : ℕ} (he : e < q.m) :
    lam q.m (Ls ++ [cur ++ [e]]) = putIn Ls.length (lam q.m (Ls ++ [cur])) ⟨e, he⟩ := by sorry
