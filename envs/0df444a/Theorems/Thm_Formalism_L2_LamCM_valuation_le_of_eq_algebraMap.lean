-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_valuation_le_of_eq_algebraMap
-- name    : Formalism.L2.LamCM.valuation_le_of_eq_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:17.575162+00:00
-- url     : https://prove2.me/theorems/03727dad-2c0a-4246-892d-9256be123510
-- title:
--   Lam CM: valuation le of eq algebra Map
-- statement:
--   The Lam CM construction uses the valuation le of eq algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L46-L54

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

theorem Formalism.L2.LamCM.valuation_le_of_eq_algebraMap {K' R : Type} [Field K'] [CommRing R] [Algebra R K']
    (p : HeightOneSpectrum (𝓞 K)) (f : K →+* K')
    (hval : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) {k c : K} (hc : c ≠ 0) (w : R)
    (hw : f (k / c) = algebraMap R K' w) : p.valuation K k ≤ p.valuation K c := by sorry
