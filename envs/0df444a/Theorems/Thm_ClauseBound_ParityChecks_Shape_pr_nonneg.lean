-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_pr_nonneg
-- name    : ClauseBound.ParityChecks.Shape.pr_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:49:12.05082+00:00
-- url     : https://prove2.me/theorems/3a566703-0e2a-415f-b622-2160be640a16
-- title:
--   Shape: pr nonneg
-- statement:
--   `pr nb` = 1/nb ≥ 0 (this is not the p of Appendix D of the paper).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L31-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L31-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.pr_nonneg (nb : ℕ) : 0 ≤ pr nb := by sorry
