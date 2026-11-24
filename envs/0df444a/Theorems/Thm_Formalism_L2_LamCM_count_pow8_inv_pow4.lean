-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_count_pow8_inv_pow4
-- name    : Formalism.L2.LamCM.count_pow8_inv_pow4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:13.016702+00:00
-- url     : https://prove2.me/theorems/657dab18-83db-40bc-b6c0-03c9b8f48af3
-- title:
--   Lam CM: count pow8 inv pow4
-- statement:
--   The Lam CM construction uses the count pow8 inv pow4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L16-L23

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

theorem Formalism.L2.LamCM.count_pow8_inv_pow4 (p : HeightOneSpectrum (𝓞 K)) {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0)
    (hB : B ≠ 0) :
    FractionalIdeal.count K p (A ^ 8 * (B ^ 4)⁻¹) =
      8 * FractionalIdeal.count K p A - 4 * FractionalIdeal.count K p B := by sorry
