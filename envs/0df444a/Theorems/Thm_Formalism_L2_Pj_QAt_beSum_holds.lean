-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_beSum_holds
-- name    : Formalism.L2.Pj.QAt.beSum_holds
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:09.640703+00:00
-- url     : https://prove2.me/theorems/83f4c39a-4e9a-4af7-aa7b-250e96a9c5b4
-- title:
--   QAt: be Sum holds
-- statement:
--   The QAt construction uses the be Sum holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L54-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinitePlaceArcs/BeSumPf.lean#L54-L122

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open BeSumPf

theorem Formalism.L2.Pj.QAt.beSum_holds : BeSumStatement := by sorry
