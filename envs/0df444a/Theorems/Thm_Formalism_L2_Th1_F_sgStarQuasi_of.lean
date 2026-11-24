-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sgStarQuasi_of
-- name    : Formalism.L2.Th1.F.sgStarQuasi_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:35.467594+00:00
-- url     : https://prove2.me/theorems/6e6550ed-6954-4b0b-83a1-51d8ae8454f8
-- title:
--   F: sg Star Quasi of
-- statement:
--   The F construction uses the sg Star Quasi of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L24-L36

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
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
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds

theorem Formalism.L2.Th1.F.sgStarQuasi_of (hq : SigmaQuasi) (he : EtaSplit) : SgStarQuasi := by sorry
