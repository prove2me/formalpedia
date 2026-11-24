-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_USer_uSerLattice_gen
-- name    : Formalism.L2.Th1.F.USer.uSerLattice_gen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:44.919431+00:00
-- url     : https://prove2.me/theorems/e238d712-fbe9-464d-8114-c8983e6d7379
-- title:
--   USer: u Ser Lattice gen
-- statement:
--   The USer construction uses the u Ser Lattice gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/GoodModelLatticeGen.lean#L134-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/GoodModelLatticeGen.lean#L134-L174

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries TaylorWp
open Formalism.L2.Th1.F.USer

theorem Formalism.L2.Th1.F.USer.uSerLattice_gen (hr : TaylorRing) (hd : TaylorDeriv) (hp : POfLattice) (hn : WpNumDen) :
    USerLattice := by sorry
