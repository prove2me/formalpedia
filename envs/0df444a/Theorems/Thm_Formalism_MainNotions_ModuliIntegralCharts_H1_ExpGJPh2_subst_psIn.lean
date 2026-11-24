-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh2_subst_psIn
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2.subst_psIn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:41.988033+00:00
-- url     : https://prove2.me/theorems/993441e3-1d10-4d87-9bc2-9e3a4d4e9d58
-- title:
--   Exp GJPh2: subst ps In
-- statement:
--   The Exp GJPh2 construction uses the subst ps In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhTwoValHolds.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhTwoValHolds.lean#L43-L49

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2.subst_psIn {d n n' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (r : Fin n → Fin n')
    (Q : Fin n' × Fin d → MvPowerSeries κ S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (f : MvPowerSeries (Fin n × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m r f : MvPolynomial _ S) : MvPowerSeries _ S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin n × Fin d => Q (r p.1, p.2)) f) := by sorry
