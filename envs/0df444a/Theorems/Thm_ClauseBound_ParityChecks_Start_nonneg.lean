-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_nonneg
-- name    : ClauseBound.ParityChecks.Start.nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:42.314439+00:00
-- url     : https://prove2.me/theorems/c49dd5a4-7dc6-4bf0-a7eb-24857a8d03fd
-- title:
--   Start: nonneg
-- statement:
--   All four terms of the potential are nonnegative.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L171-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L171-L183

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset

theorem ClauseBound.ParityChecks.Start.nonneg : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E), 2 ≤ nb →
    0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D := by sorry
