-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_numO_div_den
-- name    : ClauseBound.ParityChecks.Run.numO_div_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:59.50119+00:00
-- url     : https://prove2.me/theorems/4223aa19-be45-44c5-9e04-b5ba3a24e5e0
-- title:
--   Run: num O div den
-- statement:
--   In a state that satisfies the bounds for states that are tried, the numerator that the run
--   computes, over the denominator, is the truncated potential.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L216-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L216-L234

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}

theorem ClauseBound.ParityChecks.Run.numO_div_den (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) (hT : Tent q (lam q.m (Ls ++ [cur]))) :
    (q.numO orcA orcB Ls cur e : ℚ) / q.den Ls.length = tUU q V Ls cur e := by sorry
