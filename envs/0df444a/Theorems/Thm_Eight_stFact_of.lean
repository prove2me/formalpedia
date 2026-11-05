-- Prove2me | Theorems.Thm_Eight_stFact_of
-- name    : Eight.stFact_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:02.179386+00:00
-- url     : https://prove2.me/theorems/e5d0446f-a22f-4e7d-ac7b-47dd0ec29f30
-- title:
--   Eight: st Fact of
-- statement:
--   **Lemma 2(b)** for the programs `fTop` and `fBot`, from the factorization for one Q, the
--   correctness of `aMul` and the sum over the sets Q. The three hypotheses are filled in by `stFact`
--   (proof/networks/Eight/SecCrossing_LemPieces.lean). The bounds hold for every list θ, of any length,
--   which is more than the paper asks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L273-L281
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L273-L281

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.stFact_of (hC : StChunk) (hA : StAMul) (hS : StSubsets) : StFact := by sorry
