-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_eq_zero_of_mem
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_eq_zero_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:26.91285+00:00
-- url     : https://prove2.me/theorems/9312c2fb-9cca-4b2f-a658-0a801b83fd55
-- title:
--   Germ Fun: coeff eq zero of mem
-- statement:
--   The Germ Fun construction uses the coeff eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L162-L166

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_eq_zero_of_mem {R ι : Type} [CommRing R] {n : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ orig R ι ^ n) {e : ι →₀ ℕ} (he : e.degree < n) : MvPolynomial.coeff e p = 0 := by sorry
