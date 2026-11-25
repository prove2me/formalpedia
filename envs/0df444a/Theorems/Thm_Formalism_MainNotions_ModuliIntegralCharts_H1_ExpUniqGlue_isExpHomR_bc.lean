-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_isExpHomR_bc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.isExpHomR_bc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:20.536708+00:00
-- url     : https://prove2.me/theorems/ef7bb0a1-b7cd-4bde-a48c-f519f74b73e2
-- title:
--   Exp Uniq Glue: is Exp Hom R bc
-- statement:
--   The Exp Uniq Glue construction uses the is Exp Hom R bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L112-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L112-L151

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.isExpHomR_bc {x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G} (hx : IsExpHomR x0 d x) :
    IsExpHomR (x0T f x0) d (xT f x0 x) := by sorry
