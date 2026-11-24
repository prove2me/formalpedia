-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_valuation_eq_exp_count
-- name    : Formalism.L2.LamCM.valuation_eq_exp_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:34.976282+00:00
-- url     : https://prove2.me/theorems/c79126bd-735e-400c-8918-956a5a7b26e3
-- title:
--   Lam CM: valuation eq exp count
-- statement:
--   The Lam CM construction uses the valuation eq exp count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L44-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L44-L62

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by sorry
