-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_locMap_mk
-- name    : Formalism.L2.Pj.QAt.TieLDB.locMap_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:29.427928+00:00
-- url     : https://prove2.me/theorems/d1669098-0daf-4bc4-b087-744c17487ffe
-- title:
--   Tie LDB: loc Map mk
-- statement:
--   The Tie LDB construction uses the loc Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L77-L78

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

theorem Formalism.L2.Pj.QAt.TieLDB.locMap_mk (h : H) :
    locMap p H G (Submodule.Quotient.mk h) = Submodule.Quotient.mk (inc p H h) := by sorry
