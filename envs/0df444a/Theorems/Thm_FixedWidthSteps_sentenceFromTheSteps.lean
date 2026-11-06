-- Prove2me | Theorems.Thm_FixedWidthSteps_sentenceFromTheSteps
-- name    : FixedWidthSteps.sentenceFromTheSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:18:15.847411+00:00
-- url     : https://prove2.me/theorems/1e0ab677-5bb0-474e-81bf-58b6d7f577c2
-- title:
--   Fixed Width Steps: sentence From The Steps
-- statement:
--   The second statement of Theorem A (c) (the bound in n for fixed width k, under its proviso),
--   from the steps of its proof.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Sentence.lean#L26-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Sentence.lean#L26-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_FixedWidthSteps_Sentence
set_option autoImplicit false
section
section
open FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth

theorem FixedWidthSteps.sentenceFromTheSteps : SentenceFromTheSteps := by sorry
