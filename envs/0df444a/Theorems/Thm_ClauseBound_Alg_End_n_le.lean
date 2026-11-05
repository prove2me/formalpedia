-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_n_le
-- name    : ClauseBound.Alg.End.n_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:08:58.252376+00:00
-- url     : https://prove2.me/theorems/8d7875c3-78b1-42b5-9a5f-1f69177ac65c
-- title:
--   End: n le
-- statement:
--   If every variable occurs in a k-CNF with m clauses then n ≤ k·m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L91-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L91-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_n_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.n_le {k n : ℕ} {φ : Sat3.CNF n} (h : SatK.IsKCNF k φ) (ho : SatM.AllOccur φ) : n ≤ k * φ.length := by sorry
