-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_ev2
-- name    : ClauseBound.ParityChecks.Count.ev2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:37.157966+00:00
-- url     : https://prove2.me/theorems/2070ad5e-6df8-4425-bcac-b78cba39843c
-- title:
--   Count: ev2
-- statement:
--   The same on the first two layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L147-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L147-L157

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

theorem ClauseBound.ParityChecks.Count.ev2 (Lam : List Chk) (j : ℕ) (hj : j ≤ r) (hLam : ∀ L ∈ Lam, ChkOK ψ.length L) (hT : Tent (mkQ ψ nb r i₀ β) (lam ψ.length Lam))
    (ws : List ℤ) (lo hi : List ℕ) (hhi : ∀ l < 2, hi.getD l 0 ≤ β - 1 + r) :
    evW S k pad i n Δ (mkQ ψ nb r i₀ β) ws lo hi [ψ, incL n ψ Lam j] = truncW (n + r) ws lo hi [ψ, incL n ψ Lam j] := by sorry
