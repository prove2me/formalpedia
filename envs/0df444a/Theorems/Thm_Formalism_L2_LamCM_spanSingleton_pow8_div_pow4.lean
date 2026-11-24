-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_spanSingleton_pow8_div_pow4
-- name    : Formalism.L2.LamCM.spanSingleton_pow8_div_pow4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.366418+00:00
-- url     : https://prove2.me/theorems/17a8e30b-8787-4b8d-9d15-e56207aa682f
-- title:
--   Lam CM: span Singleton pow8 div pow4
-- statement:
--   The Lam CM construction uses the span Singleton pow8 div pow4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L25-L29

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

theorem Formalism.L2.LamCM.spanSingleton_pow8_div_pow4 (a b : K) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (a ^ 8 / b ^ 4) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a ^ 8 * (FractionalIdeal.spanSingleton (𝓞 K)⁰ b ^ 4)⁻¹ := by sorry
