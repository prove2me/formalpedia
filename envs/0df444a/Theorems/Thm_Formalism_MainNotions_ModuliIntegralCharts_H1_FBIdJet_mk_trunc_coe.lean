-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:22.758746+00:00
-- url     : https://prove2.me/theorems/de8784c2-c840-4e3f-8f4d-32b5a1d030bb
-- title:
--   FBId Jet: mk trunc coe
-- statement:
--   The FBId Jet construction uses the mk trunc coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L83-L92

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : MvPolynomial ι R) :
    (Ideal.Quotient.mk (orig R ι ^ (m + 1))
      (MvPowerSeries.truncTotal (m + 1) (P : MvPowerSeries ι R))) = Ideal.Quotient.mk _ P := by sorry
