-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:23.070136+00:00
-- url     : https://prove2.me/theorems/5e81d16c-2ce1-4690-8946-ec01c92c60fb
-- title:
--   FBId Jet: ps Trunc eq
-- statement:
--   The FBId Jet construction uses the ps Trunc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L13-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L13-L58

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) :
    psTrunc m f = MvPowerSeries.truncTotal (m + 1) f := by sorry
