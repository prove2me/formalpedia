-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_aeval_coe_comp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.aeval_coe_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:08.641045+00:00
-- url     : https://prove2.me/theorems/6bcfdb01-68f1-42da-a64a-66775e694f6c
-- title:
--   FBId Jet: aeval coe comp
-- statement:
--   The FBId Jet construction uses the aeval coe comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L197-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L197-L209

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.aeval_coe_comp {σ τ : Type} (A : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => (A i : MvPowerSeries τ R)) P =
      ((MvPolynomial.aeval A P : MvPolynomial τ R) : MvPowerSeries τ R) := by sorry
