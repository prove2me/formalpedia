-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_iterate_pderiv
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_iterate_pderiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:17.632167+00:00
-- url     : https://prove2.me/theorems/530a90f7-e21b-4334-8fd0-b5334ee714e1
-- title:
--   KAV: coeff iterate pderiv
-- statement:
--   The KAV construction uses the coeff iterate pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L36-L49

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_iterate_pderiv {σ R : Type} [CommRing R] (i : σ) (k : ℕ) :
    ∀ (F : MvPowerSeries σ R) (N : σ →₀ ℕ), coeff N ((pderiv R i)^[k] F) =
      (∏ t ∈ Finset.range k, ((N i + t + 1 : ℕ) : R)) * coeff (N + k • Finsupp.single i 1) F := by sorry
