-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_val_coeff_pow
-- name    : Formalism.IncomingBounds.thmPExp_val_coeff_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:26.542888+00:00
-- url     : https://prove2.me/theorems/95fa314c-87fb-4f9f-b1c8-7942ad28555e
-- title:
--   Incoming Bounds: thm PExp val coeff pow
-- statement:
--   The Incoming Bounds construction uses the thm PExp val coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L132-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L132-L156

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

theorem Formalism.IncomingBounds.thmPExp_val_coeff_pow {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) {σ : Type}
    (w : (σ →₀ ℕ) → ℝ) (hw : ∀ m m', w (m + m') = w m + w m') (c : ℝ)
    (h : MvPowerSeries σ K) (hh : ∀ m, ((c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m h)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), (((k : ℝ) * c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m (h ^ k)) := by sorry
