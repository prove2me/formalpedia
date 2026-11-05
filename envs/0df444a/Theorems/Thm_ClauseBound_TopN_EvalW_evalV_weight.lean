-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_evalV_weight
-- name    : ClauseBound.TopN.EvalW.evalV_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:58.77875+00:00
-- url     : https://prove2.me/theorems/77e4c351-f919-4f23-9b73-7ea36f89b602
-- title:
--   Eval W: eval V weight
-- statement:
--   One evaluation with the weight G of the numbers of marks per layer is the sum over the
--   assignments σ and the sets P of violated clauses with at most w members in every layer of
--   G (numbers of members of P in the layers) times the sign of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L124-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L124-L134

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

theorem ClauseBound.TopN.EvalW.evalV_weight (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (p : U × U × U × U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < p.2.2.2.length) (hb' : p.2.2.2.length ≤ 2 ^ p.2.2.1.length) (hW : WfL k p.1.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length p.1.length p.2.1.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y)) = (markN gu.length ((gu, p.1, p.2.2.1, p.2.2.2), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) p Ls =
      ∑ σ : Fin p.1.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ p.2.1.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by sorry
