-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_rounds
-- name    : ClauseBound.Gen.Pick.rounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:18.245797+00:00
-- url     : https://prove2.me/theorems/60d3ab95-f3b6-4174-9ac9-abca80d26f8f
-- title:
--   Pick: rounds
-- statement:
--   After r rounds the state is that of a level ℓ ≤ r with ℓ = 0 or K_ℓ ≤ b, and ℓ = r unless b <
--   K_{ℓ+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L139-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L139-L163

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.rounds (P : PiecesF) (x₀ : ℕ) (b : U) : ∀ r ≤ b.length, ∃ l,
    (List.replicate r ()).foldl (fun st _ => cap (padOf P.m x₀ b) ([], [], [], [], []) (next b st))
      (cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ 0)) = state P x₀ l ∧
    l ≤ r ∧ (l = 0 ∨ K x₀ l ≤ b.length) ∧ (r ≤ l ∨ b.length < K x₀ (l + 1)) := by sorry
