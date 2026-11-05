-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_tUpar_eq
-- name    : ClauseBound.ParityChecks.Num.tUpar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:16.269234+00:00
-- url     : https://prove2.me/theorems/7aaa3026-7f4b-46c0-8749-760b168cf67e
-- title:
--   Num: t Upar eq
-- statement:
--   The truncated Υ_par = (5/8)^k·½·numP/nb^i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L278-L283
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L278-L283

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

theorem ClauseBound.ParityChecks.Num.tUpar_eq (hnb : 1 ≤ q.nb) (j : ℕ) (Λ : ℕ → Finset (Fin q.m)) (D : Finset (Fin q.m)) :
    tUpar V q.nb q.r q.i₀ j Λ D =
      (5 / 8) ^ q.k j * (1 / 2) * ((q.numP (Aint V q.nb j Λ) (fun i => Bint V q.nb i j Λ D) : ℚ) / (q.nb : ℚ) ^ q.i₀) := by sorry
