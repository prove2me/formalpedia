-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_isLocGen_inv
-- name    : Formalism.L2.LamCM.isLocGen_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:37.508499+00:00
-- url     : https://prove2.me/theorems/e3d778df-aa7a-49dd-833f-00a36dc9706f
-- title:
--   Lam CM: is Loc Gen inv
-- statement:
--   The Lam CM construction uses the is Loc Gen inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ValuationLeOfEqAlgebraMap.lean#L41-L44

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

theorem Formalism.L2.LamCM.isLocGen_inv {p : HeightOneSpectrum (𝓞 K)} {c : K} {I : FractionalIdeal (𝓞 K)⁰ K}
    (h : IsLocGen p c I) : IsLocGen p c⁻¹ I⁻¹ := by sorry
