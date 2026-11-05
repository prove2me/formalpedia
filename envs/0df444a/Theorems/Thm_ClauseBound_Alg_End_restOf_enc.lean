-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_restOf_enc
-- name    : ClauseBound.Alg.End.restOf_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:06.488491+00:00
-- url     : https://prove2.me/theorems/89dad0be-379d-4879-94cd-e3dc33f85317
-- title:
--   End: rest Of enc
-- statement:
--   After 1ᵏ 0 comes the code of φ as an instance of k-SAT.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L36-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.restOf_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : restOf (SatM.enc k φ) = SatK.enc k φ := by sorry
