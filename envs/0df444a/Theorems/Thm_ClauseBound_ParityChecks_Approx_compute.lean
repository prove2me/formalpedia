-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_compute
-- name    : ClauseBound.ParityChecks.Approx.compute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:06.583181+00:00
-- url     : https://prove2.me/theorems/8f1e0ff1-0c28-429a-9038-d83fd0d17d2f
-- title:
--   Approx: compute
-- statement:
--   The truncated potential through the integers A and B_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L98-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L98-L111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]

theorem ClauseBound.ParityChecks.Approx.compute (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    tUpar V nb r i₀ j Λ D =
      (5 / 8) ^ (r - 1 - j) * (1 / 2) * ((Aint V nb j Λ : ℚ) + ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (Bint V nb i j Λ D : ℚ)) := by sorry
