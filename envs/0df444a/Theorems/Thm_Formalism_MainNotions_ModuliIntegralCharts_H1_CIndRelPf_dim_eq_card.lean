-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndRelPf_dim_eq_card
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf.dim_eq_card
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:54.425168+00:00
-- url     : https://prove2.me/theorems/a20e2642-7464-48d4-838a-16e7ab6d9868
-- title:
--   CInd Rel Pf: dim eq card
-- statement:
--   The CInd Rel Pf construction uses the dim eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndRelPf.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndRelPf.lean#L12-L37

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRelPf
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
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf.dim_eq_card {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Fintype ι] {d : ℕ}
    (u : ι → Fin d → S) (h : ∀ v : Fin d → S, ∃! a : ι → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    d = Fintype.card ι := by sorry
