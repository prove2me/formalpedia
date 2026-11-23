-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_gen_eq_of_corr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.gen_eq_of_corr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:36.305254+00:00
-- url     : https://prove2.me/theorems/c9116d04-1500-43c3-8808-a7cd92395218
-- title:
--   Germ Fun: gen eq of corr
-- statement:
--   The Germ Fun construction uses the gen eq of corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L28-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermFunPf.lean#L28-L74

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.gen_eq_of_corr {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type}
    [Fintype K'] (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t₁ t₂ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (g : LB.Gen (LB.LinComb L φ' ε')) (h₁ : LB.Gen.Corr L _ _ _ _ t₁ g)
    (h₂ : LB.Gen.Corr L _ _ _ _ t₂ g) : t₁ = t₂ := by sorry
