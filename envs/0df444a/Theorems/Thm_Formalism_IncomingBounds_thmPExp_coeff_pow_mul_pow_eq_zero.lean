-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_coeff_pow_mul_pow_eq_zero
-- name    : Formalism.IncomingBounds.thmPExp_coeff_pow_mul_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:36.706188+00:00
-- url     : https://prove2.me/theorems/9f7149ed-7233-42b0-b6ee-fea521f928e4
-- title:
--   Incoming Bounds: thm PExp coeff pow mul pow eq zero
-- statement:
--   The Incoming Bounds construction uses the thm PExp coeff pow mul pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L19-L29

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

theorem Formalism.IncomingBounds.thmPExp_coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {m : σ →₀ ℕ} {j j' : ℕ} (hk : m.degree < j + j') :
    coeff m (a ^ j * b ^ j') = 0 := by sorry
