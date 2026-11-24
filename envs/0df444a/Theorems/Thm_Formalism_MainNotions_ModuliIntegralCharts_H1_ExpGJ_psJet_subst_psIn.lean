-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJ_psJet_subst_psIn
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ.psJet_subst_psIn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:39.681695+00:00
-- url     : https://prove2.me/theorems/74dc6143-7e23-4268-9260-deff72a0657b
-- title:
--   Exp GJ: ps Jet subst ps In
-- statement:
--   The Exp GJ construction uses the ps Jet subst ps In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpGJAd.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpGJAd.lean#L42-L52

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpGJAd
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {d n : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ.psJet_subst_psIn {ι' : Type} [Fintype ι'] [DecidableEq ι'] (m : ℕ) (i : Fin n)
    (Q : Fin n × Fin d → MvPowerSeries ι' S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (g : MvPowerSeries (Fin 1 × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m ![i] g : MvPolynomial (Fin n × Fin d) S) : MvPowerSeries (Fin n × Fin d) S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin 1 × Fin d => Q (i, p.2)) g) := by sorry
