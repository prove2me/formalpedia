-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_jetSubstPS_psJet
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf.jetSubstPS_psJet
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:05.705827+00:00
-- url     : https://prove2.me/theorems/9338c74f-6a69-476c-a829-4dcedc34891c
-- title:
--   Exp Tie Pf: jet Subst PS ps Jet
-- statement:
--   The Exp Tie Pf construction uses the jet Subst PS ps Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L191-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTiePf.lean#L191-L267

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf.jetSubstPS_psJet {S : Type} [CommRing S] {d N : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
    (h0 : ∀ j, constantCoeff (φ j) = 0) (m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    (jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2)) (psJet m f) =
      psJet m (subst (fun p : Fin 1 × Fin d => φ p.2) f) := by sorry
