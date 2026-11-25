-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_tensor_eq_top
-- name    : Formalism.L2.Pj.QAt.TieLDA.length_tensor_eq_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:13.224558+00:00
-- url     : https://prove2.me/theorems/42d8444e-13c0-4691-ad35-cb9f5ccfdfe5
-- title:
--   Tie LDA: length tensor eq top
-- statement:
--   The Tie LDA construction uses the length tensor eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L312-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L312-L347

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module

theorem Formalism.L2.Pj.QAt.TieLDA.length_tensor_eq_top {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra R T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] (h : Module.length R N = ⊤) :
    Module.length T (T ⊗[R] N) = ⊤ := by sorry
