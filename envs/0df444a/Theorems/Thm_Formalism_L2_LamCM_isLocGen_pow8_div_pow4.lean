-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_isLocGen_pow8_div_pow4
-- name    : Formalism.L2.LamCM.isLocGen_pow8_div_pow4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:05.078332+00:00
-- url     : https://prove2.me/theorems/23a59dae-d51b-4b8e-a9b4-78b0fba16add
-- title:
--   Lam CM: is Loc Gen pow8 div pow4
-- statement:
--   The Lam CM construction uses the is Loc Gen pow8 div pow4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L31-L39

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

theorem Formalism.L2.LamCM.isLocGen_pow8_div_pow4 {p : HeightOneSpectrum (𝓞 K)} {ca cd : K} {A B : FractionalIdeal (𝓞 K)⁰ K}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : IsLocGen p ca A) (hb : IsLocGen p cd B) :
    IsLocGen p (ca ^ 8 / cd ^ 4) (A ^ 8 * (B ^ 4)⁻¹) := by sorry
