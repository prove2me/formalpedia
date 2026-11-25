-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_coeff_mvExp
-- name    : Formalism.IncomingBounds.thmPExp_coeff_mvExp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:54.602018+00:00
-- url     : https://prove2.me/theorems/dd325e3b-e6b1-42a5-b682-fb488fc728e8
-- title:
--   Incoming Bounds: thm PExp coeff mv Exp
-- statement:
--   The Incoming Bounds construction uses the thm PExp coeff mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L31-L38

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}

theorem Formalism.IncomingBounds.thmPExp_coeff_mvExp {h : MvPowerSeries σ C} (hh : constantCoeff h = 0)
    (m : σ →₀ ℕ) {N : ℕ} (hN : m.degree < N) :
    coeff m (mvExp h) = ∑ k ∈ range N, coeff m (h ^ k) / (k.factorial : C) := by sorry
