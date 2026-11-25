-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_mk_rename
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.mk_rename
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:05.722677+00:00
-- url     : https://prove2.me/theorems/ff88216f-df2d-4793-ab0c-027d11822148
-- title:
--   FBId Ph: mk rename
-- statement:
--   The FBId Ph construction uses the mk rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ThetaSwapFirstTwo.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ThetaSwapFirstTwo.lean#L123-L130

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (d : ℕ)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.mk_rename {κ κ' : Type} (m : ℕ) (ρ : κ → κ') (P : MvPolynomial κ S) :
    (Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (rename ρ P)) =
      jetMap (m := m) (fun i => (X (ρ i) : MvPolynomial κ' S)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by sorry
