-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_sum_encP
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.sum_encP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:00.644005+00:00
-- url     : https://prove2.me/theorems/c36e3981-ec0e-455b-9c00-957639bc9d30
-- title:
--   KAV: sum enc P
-- statement:
--   The KAV construction uses the sum enc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L111-L126

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.sum_encP {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) (P : MvPolynomial (LtN Dw n) K)
    (V : ((Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n →₀ ℕ) → S) :
    ∑ m' ∈ (MvPolynomial.map φ (encP P)).support, (MvPolynomial.map φ (encP P)).coeff m' * V m' =
      ∑ m ∈ P.support, φ (P.coeff m) * V (Finsupp.equivMapDomain (ltEquiv Dw n) m) := by sorry
