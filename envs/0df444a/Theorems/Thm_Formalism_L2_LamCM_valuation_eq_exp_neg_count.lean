-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_valuation_eq_exp_neg_count
-- name    : Formalism.L2.LamCM.valuation_eq_exp_neg_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:59.887584+00:00
-- url     : https://prove2.me/theorems/d5e6fef6-a444-45d5-951d-12135ba5f8ce
-- title:
--   Lam CM: valuation eq exp neg count
-- statement:
--   The Lam CM construction uses the valuation eq exp neg count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L62-L84

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
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
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.valuation_eq_exp_neg_count (p : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    p.valuation K x =
      WithZero.exp (-FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by sorry
