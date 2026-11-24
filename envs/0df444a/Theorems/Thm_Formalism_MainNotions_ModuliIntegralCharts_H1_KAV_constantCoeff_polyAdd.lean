-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_constantCoeff_polyAdd
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.constantCoeff_polyAdd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:41.836792+00:00
-- url     : https://prove2.me/theorems/781593c5-f3b1-45be-8db2-4879b5f68a48
-- title:
--   KAV: constant Coeff poly Add
-- statement:
--   The KAV construction uses the constant Coeff poly Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L86-L103

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.constantCoeff_polyAdd {S : Type} [CommRing S] {d n : ℕ} {ι : Type} [Fintype ι] (e : ι → Fin d)
    (he : Function.Injective e) (P : MvPolynomial (ι × Fin n) S) (G : Germ.PS S n d) :
    constantCoeff (TB.polyAdd (fun l => Pi.single (e l) 1) P G) =
      ∑ m ∈ P.support, P.coeff m * ((∏ p, ((m p).factorial : S)) *
        coeff (∑ p, m p • Finsupp.single (p.2, e p.1) 1) G) := by sorry
