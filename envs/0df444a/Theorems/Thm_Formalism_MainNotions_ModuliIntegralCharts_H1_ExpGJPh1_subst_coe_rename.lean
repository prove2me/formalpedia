-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh1_subst_coe_rename
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.subst_coe_rename
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:59.688379+00:00
-- url     : https://prove2.me/theorems/7bf90ea5-0ab6-4b81-a68f-a9e15ded7e05
-- title:
--   Exp GJPh1: subst coe rename
-- statement:
--   The Exp GJPh1 construction uses the subst coe rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SubstCoeRename.lean#L16-L32

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SubstCoeRename
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.subst_coe_rename {σ τ υ : Type} {R : Type} [CommRing R] [Finite σ] [Finite τ] (a : σ → MvPowerSeries υ R)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ) (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by sorry
