-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqTan_eq_zero_of_tan
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.eq_zero_of_tan
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:13.286869+00:00
-- url     : https://prove2.me/theorems/514174fe-f972-4454-a44b-ae27ef1cd60b
-- title:
--   Exp Uniq Tan: eq zero of tan
-- statement:
--   The Exp Uniq Tan construction uses the eq zero of tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqTan.lean#L90-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqTan.lean#L90-L106

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.eq_zero_of_tan {κ : Type} [Fintype κ] [DecidableEq κ] (p : Jet R κ (0 + 1)) (hp : p ∈ Ij R κ (0 + 1))
    (ht : ∀ ℓ, (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) p = 0) : p = 0 := by sorry
