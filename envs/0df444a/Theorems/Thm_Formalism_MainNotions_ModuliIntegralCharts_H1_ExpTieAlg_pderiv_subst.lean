-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_subst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:08.299804+00:00
-- url     : https://prove2.me/theorems/e4798058-1dd9-4c91-9bba-e126bd1be907
-- title:
--   Exp Tie Alg: pderiv subst
-- statement:
--   The Exp Tie Alg construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L24-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L24-L67

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
open scoped MvPowerSeries.WithPiTopology

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (t : τ) (g : MvPowerSeries σ S) :
    pderiv S t (subst a g) = ∑ s, subst a (pderiv S s g) * pderiv S t (a s) := by sorry
