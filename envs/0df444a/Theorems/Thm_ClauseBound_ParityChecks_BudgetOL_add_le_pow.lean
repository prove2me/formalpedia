-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_add_le_pow
-- name    : ClauseBound.ParityChecks.BudgetOL.add_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:42:37.295727+00:00
-- url     : https://prove2.me/theorems/960d9c2d-aa33-4c73-b054-109eef927c5e
-- title:
--   Budget OL: add le pow
-- statement:
--   A sum of two numbers below powers of two.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L31-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L31-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)

theorem ClauseBound.ParityChecks.BudgetOL.add_le_pow {x y p q r : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) (hp : p < r) (hq : q < r) : x + y ≤ 2 ^ r := by sorry
