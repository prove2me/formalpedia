-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_mem_ordGE
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.mem_ordGE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:36.562012+00:00
-- url     : https://prove2.me/theorems/511755de-baee-4c74-9ae0-abebfa69f7e7
-- title:
--   Germ Fun: mem ord GE
-- statement:
--   The Germ Fun construction uses the mem ord GE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L126-L127

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.mem_ordGE {R ι : Type} [CommRing R] {n : ℕ} {p : MvPolynomial ι R} :
    p ∈ ordGE R ι n ↔ ∀ e ∈ p.support, n ≤ e.degree := by sorry
