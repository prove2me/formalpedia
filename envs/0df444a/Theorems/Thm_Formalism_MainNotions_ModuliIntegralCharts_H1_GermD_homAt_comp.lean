-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:16.393366+00:00
-- url     : https://prove2.me/theorems/d70b11df-83a2-40f9-a165-9c00eae15946
-- title:
--   Germ D: hom At comp
-- statement:
--   The Germ D construction uses the hom At comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L185-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L185-L189

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by sorry
