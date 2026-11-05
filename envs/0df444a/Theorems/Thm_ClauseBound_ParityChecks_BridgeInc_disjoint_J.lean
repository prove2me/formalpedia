-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_disjoint_J
-- name    : ClauseBound.ParityChecks.BridgeInc.disjoint_J
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:42.094196+00:00
-- url     : https://prove2.me/theorems/73072143-5972-4944-896b-04edb703a9e2
-- title:
--   Bridge Inc: disjoint J
-- statement:
--   The Bridge Inc construction uses the disjoint J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L160-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L160-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.disjoint_J (r j : ℕ) : Disjoint (J1 r j) (J2 r j) := by sorry
