-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_over
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_over
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:18.915126+00:00
-- url     : https://prove2.me/theorems/f264447b-f20e-5006-9d85-304c68a68569
-- title:
--   Exp Uniq Glue: nat over
-- statement:
--   The Exp Uniq Glue construction uses the nat over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean#L73-L80

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
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
variable {X : Scheme.{0}} (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp S ⟶ X)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_over {A A' B B' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] [CommRing B]
    [Algebra S B] [CommRing B'] [Algebra T B'] (bA : A →+* A') (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f)
    (bB : B →+* B') (hB : bB.comp (algebraMap S B) = (algebraMap T B').comp f)
    (ψ : A →ₐ[S] B) (ψ' : A' →ₐ[T] B') (e : (ψ' : A' →+* B').comp bA = bB.comp (ψ : A →+* B)) :
    homAt (x0T f x0) ψ' ≫ bcO f x0 bA hA = bcO f x0 bB hB ≫ homAt x0 ψ := by sorry
