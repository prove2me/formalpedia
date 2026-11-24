-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpActPf_eq_linear
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.eq_linear
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:17.695804+00:00
-- url     : https://prove2.me/theorems/5543a9af-a599-4579-b422-fc7275bc86ac
-- title:
--   Exp Act Pf: eq linear
-- statement:
--   The Exp Act Pf construction uses the eq linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L68-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L68-L93

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]
open Formalism.FG.SolveVAux

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.eq_linear {N : ℕ} (g : MvPowerSeries (Fin 1 × Fin N) S)
    (h : ∀ n : Fin 1 × Fin N →₀ ℕ, n.degree ≠ 1 → coeff n g = 0) :
    g = ∑ q, C (coeff (Finsupp.single ((0 : Fin 1), q) 1) g) * X ((0 : Fin 1), q) := by sorry
