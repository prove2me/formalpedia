-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_card_Dset
-- name    : ClauseBound.ParityChecks.Num.card_Dset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:49.331259+00:00
-- url     : https://prove2.me/theorems/c552ac3f-8923-4dc0-bc35-1d2308523dc3
-- title:
--   Num: card Dset
-- statement:
--   m − e clauses are not yet decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L90-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L90-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num

theorem ClauseBound.ParityChecks.Num.card_Dset (m e : ℕ) : #(Dset m e) = m - e := by sorry
