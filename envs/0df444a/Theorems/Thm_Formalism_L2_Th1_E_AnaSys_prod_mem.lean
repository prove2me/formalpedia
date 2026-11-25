-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AnaSys_prod_mem
-- name    : Formalism.L2.Th1.E.AnaSys.prod_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:33.091944+00:00
-- url     : https://prove2.me/theorems/83d1aef5-e3ee-53f6-a3f2-3ad058db2c61
-- title:
--   Ana Sys: prod mem
-- statement:
--   The Ana Sys construction uses the prod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/AnaSys.lean#L340-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/AnaSys.lean#L340-L379

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AnaSys
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
variable {l L ι}
variable (l L ι)

theorem Formalism.L2.Th1.E.AnaSys.prod_mem (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∈ L.lattice) :
    X ^ 2 * (gT l L ι (P + Q) * gT l L ι (P - Q)) =
      C (constantCoeff (gT l L ι Q) ^ 2) *
        (C (px (curveL l L ι) (ptOf l L ι Q)) * X ^ 2 - x2 (curveL l L ι) (ptOf l L ι P)) *
        gT l L ι P ^ 2 := by sorry
