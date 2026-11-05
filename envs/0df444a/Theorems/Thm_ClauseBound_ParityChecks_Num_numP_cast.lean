-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_numP_cast
-- name    : ClauseBound.ParityChecks.Num.numP_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:12.122122+00:00
-- url     : https://prove2.me/theorems/5d4baa7e-efa7-4d30-b0ae-9dbbb7a87081
-- title:
--   Num: num P cast
-- statement:
--   numP = nb^i₀·(A + Σ_{i ≤ i₀} (−2p)^i·B_i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L262-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L262-L275

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
variable {q}

theorem ClauseBound.ParityChecks.Num.numP_cast (hnb : 1 ≤ q.nb) (A : ℤ) (B : ℕ → ℤ) :
    (q.numP A B : ℚ) = (q.nb : ℚ) ^ q.i₀ * ((A : ℚ) + ∑ i ∈ range (q.i₀ + 1), (-2 * pr q.nb) ^ i * (B i : ℚ)) := by sorry
