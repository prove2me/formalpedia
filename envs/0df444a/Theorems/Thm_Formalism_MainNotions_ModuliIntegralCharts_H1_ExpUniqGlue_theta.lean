-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_theta
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.theta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:39:13.637925+00:00
-- url     : https://prove2.me/theorems/0a38cd53-7621-5269-a161-148a208ab862
-- title:
--   Exp Uniq Glue: theta
-- statement:
--   The Exp Uniq Glue construction uses the theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L174-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L174-L220

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.theta {S : Type} [CommRing S] (p : Ideal S) [p.IsPrime] (κ : Type) (m : ℕ) :
    ∃ θ : Jet (Localization.AtPrime p) κ m →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p,
      θ.comp (bcJ (algebraMap S (Localization.AtPrime p)) κ m) =
        algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p) := by sorry
