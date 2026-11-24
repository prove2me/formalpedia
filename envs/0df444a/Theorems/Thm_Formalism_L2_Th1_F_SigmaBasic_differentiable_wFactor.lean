-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_differentiable_wFactor
-- name    : Formalism.L2.Th1.F.SigmaBasic.differentiable_wFactor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:28.156799+00:00
-- url     : https://prove2.me/theorems/a048851b-fa52-4e95-a235-32d165ac9d84
-- title:
--   Sigma Basic: differentiable w Factor
-- statement:
--   The Sigma Basic construction uses the differentiable w Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaBasic.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaBasic.lean#L11-L13

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
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
open Formalism.L2.Th1.F.SigmaBasic

theorem Formalism.L2.Th1.F.SigmaBasic.differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) := by sorry
