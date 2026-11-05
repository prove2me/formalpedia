-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_abs_tUU_sub
-- name    : ClauseBound.ParityChecks.Run.abs_tUU_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:54.89496+00:00
-- url     : https://prove2.me/theorems/6ee5c16b-8b35-4dda-a949-ebe5bf5faf8c
-- title:
--   Run: abs t UU sub
-- statement:
--   The truncated potential differs from the potential by at most δ = ε·N/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L185-L195
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L185-L195

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
variable {V} {orcA orcB} {ε : ℚ}

theorem ClauseBound.ParityChecks.Run.abs_tUU_sub (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (Ls : List Chk) (cur : Chk) (e : ℕ) :
    |tUU q V Ls cur e - UU q V Ls cur e| ≤ 1 / 2 * ε * NN X q := by sorry
