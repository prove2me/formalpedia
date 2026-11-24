-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpActPf_subst_family_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.subst_family_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:04.480794+00:00
-- url     : https://prove2.me/theorems/d1bcff07-4977-4935-9208-1baa67e25c07
-- title:
--   Exp Act Pf: subst family comp
-- statement:
--   The Exp Act Pf construction uses the subst family comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L30-L33

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.subst_family_comp {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} {ψ : Pt S 1 d}
    (hχ : ∀ j, constantCoeff (χ j) = 0) (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : PS S 1 d) :
    subst (fam1 χ) (subst (fam1 ψ) g) = subst (fam1 fun j => subst (fam1 χ) (ψ j)) g := by sorry
