-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sigma_summable
-- name    : Formalism.L2.Th1.F.sigma_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:35.728727+00:00
-- url     : https://prove2.me/theorems/13a0fc7c-8747-4218-9db9-4f2ae27076d5
-- title:
--   F: sigma summable
-- statement:
--   The F construction uses the sigma summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L114-L119

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
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
open SigmaConv

theorem Formalism.L2.Th1.F.sigma_summable : SigmaSummable := by sorry
