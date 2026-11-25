-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AnaSys_prod_notMem
-- name    : Formalism.L2.Th1.E.AnaSys.prod_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:58.892634+00:00
-- url     : https://prove2.me/theorems/a1611fd8-5662-51dc-874c-24cad06f9c85
-- title:
--   Ana Sys: prod not Mem
-- statement:
--   The Ana Sys construction uses the prod not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/AnaSys.lean#L312-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/AnaSys.lean#L312-L338

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

theorem Formalism.L2.Th1.E.AnaSys.prod_notMem (hT : TransWpBridge) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    X ^ 2 * (gT l L ι (P + Q) * gT l L ι (P - Q)) =
      C (constantCoeff (gT l L ι Q) ^ 2) *
        (C (px (curveL l L ι) (ptOf l L ι Q)) * X ^ 2 - x2 (curveL l L ι) (ptOf l L ι P)) *
        gT l L ι P ^ 2 := by sorry
