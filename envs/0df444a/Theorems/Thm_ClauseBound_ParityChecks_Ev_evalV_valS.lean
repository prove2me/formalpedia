-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_evalV_valS
-- name    : ClauseBound.ParityChecks.Ev.evalV_valS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:40.956871+00:00
-- url     : https://prove2.me/theorems/3760aabe-4426-478a-9830-1ada3111d981
-- title:
--   Ev: eval V val S
-- statement:
--   One evaluation is exact; the numbers of nodes and of variables, the cap and the two code
--   parameters are the lengths of any lists of units, and U₀ and P₀ are any bounds for the total and the
--   size of the networks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L56-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L56-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

theorem ClauseBound.ParityChecks.Ev.evalV_valS (hV : StMarkVal) (hP : StProfSum) (hPr : StMarkPresents) (hSz : StMarkSized) (hVal : StValS)
    {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (gu nu wu βu bu : U) (D U₀ P₀ : ℕ)
    (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hok : ok i) (hK : 2 ≤ S.K i) (hgu : gu.length = 3 * S.K i ^ 8) (hb : 0 < bu.length)
    (hb' : bu.length ≤ 2 ^ βu.length) (hW : WfL k nu.length Ls) (hocc : ∀ v, (occ Ls.flatten v).length ≤ D)
    (hfl : Ls.flatten.length ≤ bu.length * (nu.length + 1)) (hhi : ∀ l < Ls.length, hi.getD l 0 ≤ wu.length)
    (hprof : nProf gu.length (cls Ls).length Ls.length ≤ pad.length)
    (hU : Ub k gu.length nu.length wu.length βu.length Ls.length ≤ U₀) (hP₀ : Pb gu.length nu.length βu.length D ≤ P₀)
    (hnet : 2 ^ needNet S i U₀ P₀ 0 ≤ pad.length) :
    evalV k pad gu (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * valS S pad i U₀ P₀ markF c) (nu, wu, βu, bu) Ls =
      truncW nu.length ws lo hi Ls := by sorry
