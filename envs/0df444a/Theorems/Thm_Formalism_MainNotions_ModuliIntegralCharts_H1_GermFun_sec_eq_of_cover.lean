-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_sec_eq_of_cover
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.sec_eq_of_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:21.153327+00:00
-- url     : https://prove2.me/theorems/2da278da-fa40-40c0-9962-c671cb2c6cad
-- title:
--   Germ Fun: sec eq of cover
-- statement:
--   The Germ Fun construction uses the sec eq of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L16-L20

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.sec_eq_of_cover {X : Scheme.{0}} {U : X.Opens} {ι : Type} (V : ι → X.Opens)
    (hle : ∀ i, V i ≤ U) (hcov : U ≤ iSup V) (s t : Γ(X, U))
    (h : ∀ i, (X.presheaf.map (homOfLE (hle i)).op).hom s = (X.presheaf.map (homOfLE (hle i)).op).hom t) :
    s = t := by sorry
