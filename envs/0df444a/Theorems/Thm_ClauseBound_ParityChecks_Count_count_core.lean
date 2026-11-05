-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_count_core
-- name    : ClauseBound.ParityChecks.Count.count_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:16.595029+00:00
-- url     : https://prove2.me/theorems/6184d92e-ea08-4602-9714-30047a2fb9c7
-- title:
--   Count: count core
-- statement:
--   The count is right, for parameters that satisfy what the choice of the checks needs, or without
--   checks if there are at most nb clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L196-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L196-L229

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
variable (hE : StEvW) (hSh : StShape) {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml)
  (nb r i₀ β : ℕ) (hok : ok i) (hK : 2 ≤ S.K i) (hW : WfL k n [ψ]) (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hmΔ : ψ.length ≤ Δ * n) (hnb : 2 ≤ nb)
  (hLD : n < 2 * (nb * LD Δ)) (hr : r ≤ 6 * n) (hcap : β - 1 + r ≤ 11 * n) (hFit : FitsOL S k i n Δ pad.length)
include hE hSh hC hok hK hW hocc hmΔ hnb hLD hr hcap hFit

theorem ClauseBound.ParityChecks.Count.count_core (hB : StBridgeB) (hA : StBridgeA) (hF : StBridgeF) (H2 : ChoiceByPotential) (ε : ℚ) (hβ : n + 2 ≤ β) (hnbn : nb ≤ n)
    (hcase : (r = 0 ∧ ψ.length ≤ nb) ∨ (Hyp (mkQ ψ nb r i₀ β) (2 ^ n) ε ∧ i₀ ≤ β - 1 + r)) :
    countOL S k pad i n Δ (mkQ ψ nb r i₀ β) ψ = nSat n ψ := by sorry
