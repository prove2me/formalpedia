-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_isLocalizedModule
-- name    : Formalism.L2.Pj.QAt.TieLDB.isLocalizedModule
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:30.698948+00:00
-- url     : https://prove2.me/theorems/d280ddd9-a7df-4a27-913a-5c50875f85f1
-- title:
--   Tie LDB: is Localized Module
-- statement:
--   The Tie LDB construction uses the is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L80-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L80-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
variable (H G : Submodule A V)

theorem Formalism.L2.Pj.QAt.TieLDB.isLocalizedModule : IsLocalizedModule p.primeCompl (locMap p H G) := by sorry
