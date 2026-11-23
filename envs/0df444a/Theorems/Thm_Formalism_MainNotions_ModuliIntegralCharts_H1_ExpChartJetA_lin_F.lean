-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_lin_F
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_F
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:26.986925+00:00
-- url     : https://prove2.me/theorems/29ff31bf-327e-4c77-a64a-6cd844a6a6d9
-- title:
--   Exp Chart Jet A: lin F
-- statement:
--   The Exp Chart Jet A construction uses the lin F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean#L212-L217

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_F {d : ℕ} (G : FGLaw R d) (v w : Fin d → R) (k : Fin d) :
    ∑ p : Fin 2 × Fin d, (![v, w] : Fin 2 → Fin d → R) p.1 p.2 *
      MvPowerSeries.coeff (Finsupp.single p 1) (G.F k) = v k + w k := by sorry
