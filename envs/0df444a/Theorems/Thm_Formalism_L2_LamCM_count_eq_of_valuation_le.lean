-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_count_eq_of_valuation_le
-- name    : Formalism.L2.LamCM.count_eq_of_valuation_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:06.278574+00:00
-- url     : https://prove2.me/theorems/9361d393-d258-4766-bb8e-59671cabdd74
-- title:
--   Lam CM: count eq of valuation le
-- statement:
--   The Lam CM construction uses the count eq of valuation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L86-L94

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

theorem Formalism.L2.LamCM.count_eq_of_valuation_le (p : HeightOneSpectrum (𝓞 K)) {k c : K} (hk : k ≠ 0) (hc : c ≠ 0)
    (h1 : p.valuation K k ≤ p.valuation K c) (h2 : p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) =
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ c) := by sorry
