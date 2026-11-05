-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_first_le_needG
-- name    : ClauseBound.Alg.NeedC.first_le_needG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:14.347259+00:00
-- url     : https://prove2.me/theorems/4c6bc257-5623-47f6-a0f1-a8748bd77fda
-- title:
--   Need C: first le need G
-- statement:
--   The bounds of the first step (the binary digits of the first sum, lam, and the binary digits of
--   B and of Kup) are at most `needG`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L50-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F

theorem ClauseBound.Alg.NeedC.first_le_needG (P : PiecesF) (Kup lam B cnt z : ℕ) (sched : List Step) :
    max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))) ≤ needG P Kup lam B cnt z sched := by sorry
