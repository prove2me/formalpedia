-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EndoZ_hasDerivAt_fP
-- name    : Formalism.L2.Th1.F.EndoZ.hasDerivAt_fP
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:06.998141+00:00
-- url     : https://prove2.me/theorems/cbdf9cdb-7769-41fc-8c00-2c28b4f5a42a
-- title:
--   Endo Z: has Deriv At f P
-- statement:
--   The Endo Z construction uses the has Deriv At f P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L209-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L209-L228

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp

theorem Formalism.L2.Th1.F.EndoZ.hasDerivAt_fP (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    HasDerivAt (fP L P) (fP L P w * mP L P w) w := by sorry
