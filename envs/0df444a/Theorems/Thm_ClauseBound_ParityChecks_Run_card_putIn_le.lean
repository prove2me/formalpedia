-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_card_putIn_le
-- name    : ClauseBound.ParityChecks.Run.card_putIn_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:46.083484+00:00
-- url     : https://prove2.me/theorems/62b1ad04-4bd5-49ed-a993-b96e136359e4
-- title:
--   Run: card put In le
-- statement:
--   The Run construction uses the card put In le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L123-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L123-L129

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

theorem ClauseBound.ParityChecks.Run.card_putIn_le (Λ : ℕ → Finset (Fin q.m)) (j : ℕ) (x : Fin q.m) (j' : ℕ) : #(putIn j Λ x j') ≤ #(Λ j') + if j' = j then 1 else 0 := by sorry
