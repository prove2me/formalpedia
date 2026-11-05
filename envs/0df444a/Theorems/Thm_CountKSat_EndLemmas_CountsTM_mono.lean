-- Prove2me | Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
-- name    : CountKSat.EndLemmas.CountsTM.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:29.779394+00:00
-- url     : https://prove2.me/theorems/dfcf1b32-058e-40ca-a3fc-1e0188a1d285
-- title:
--   Counts TM: mono
-- statement:
--   A machine that counts within t steps counts within any larger bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/EndLemmas.lean#L24-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/EndLemmas.lean#L24-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_CountKSat_EndLemmas
set_option autoImplicit false
section
open CountKSat CountKSat.EndLemmas
open Turing SatK
open scoped NNReal ENNReal

theorem CountKSat.EndLemmas.CountsTM.mono {k : ℕ} {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : CountsTM k M t) (ht : ∀ n, t n ≤ t' n) :
    CountsTM k M t' := by sorry
