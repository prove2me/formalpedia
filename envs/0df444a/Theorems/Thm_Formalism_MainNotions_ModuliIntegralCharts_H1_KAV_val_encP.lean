-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_val_encP
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.val_encP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:07.338853+00:00
-- url     : https://prove2.me/theorems/d5ff0f7c-8ca8-46af-9ea7-7450893cfe4e
-- title:
--   KAV: val enc P
-- statement:
--   The KAV construction uses the val enc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L134-L147

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.val_encP {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {S : Type} [CommRing S] (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ) :
    (∏ p, ((Finsupp.equivMapDomain (ltEquiv Dw n) m p).factorial : S)) *
        coeff (∑ p, Finsupp.equivMapDomain (ltEquiv Dw n) m p • Finsupp.single (p.2, ltIdx Dw p.1) 1) G =
      mVal G m := by sorry
