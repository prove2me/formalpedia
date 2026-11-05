-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_evalV_weight_aux
-- name    : ClauseBound.TopN.EvalW.evalV_weight_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:48.047026+00:00
-- url     : https://prove2.me/theorems/a5555549-5cdf-4c16-a68d-6b8da5049e37
-- title:
--   Eval W: eval V weight aux
-- statement:
--   `evalV_weight` with the four parameters n, w, β, b named.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L62-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L62-L119

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

theorem ClauseBound.TopN.EvalW.evalV_weight_aux (hV : StMarkVal) (hP : StProfSum) (k : ℕ) (pad gu : U) (val : MCtx → ℤ) (nu wu βu bu : U) (Ls : List Fml) (G : (ℕ → ℕ) → ℤ)
    (hg : 0 < gu.length) (hb : 0 < bu.length) (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls)
    (hpad : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hG : ∀ t t' : ℕ → ℕ, (∀ i < Ls.length, t i = t' i) → G t = G t')
    (hval : ∀ y, adm k gu.length nu.length wu.length Ls y = true → G (tl gu.length Ls y) ≠ 0 →
      val ((gu, nu, βu, bu), (Ls, y)) = (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value) :
    evalV k pad gu (fun c => G (tl gu.length c.2.1 c.2.2) * val c) (nu, wu, βu, bu) Ls =
      ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
        if ∀ i < Ls.length, (layP Ls P i).card ≤ wu.length then G (fun i => (layP Ls P i).card) * sgnP Ls P else 0 := by sorry
