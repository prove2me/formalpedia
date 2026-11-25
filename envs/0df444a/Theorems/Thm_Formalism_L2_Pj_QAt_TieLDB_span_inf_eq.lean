-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_span_inf_eq
-- name    : Formalism.L2.Pj.QAt.TieLDB.span_inf_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:36:23.137739+00:00
-- url     : https://prove2.me/theorems/44d2cbb1-ec38-4b0b-a4ed-4725b6f05bef
-- title:
--   Tie LDB: span inf eq
-- statement:
--   The Tie LDB construction uses the span inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L37-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean#L37-L55

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

theorem Formalism.L2.Pj.QAt.TieLDB.span_inf_eq (M : Submodule A V) (W : Submodule (Localization.AtPrime p) V) :
    Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) =
      Submodule.span (Localization.AtPrime p) (M : Set V) ⊓ W := by sorry
