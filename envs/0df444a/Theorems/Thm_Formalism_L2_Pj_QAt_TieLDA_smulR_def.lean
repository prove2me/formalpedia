-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_smulR_def
-- name    : Formalism.L2.Pj.QAt.TieLDA.smulR_def
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:46.135594+00:00
-- url     : https://prove2.me/theorems/fe7d821c-36f6-41dc-aa64-069c9c133066
-- title:
--   Tie LDA: smul R def
-- statement:
--   The Tie LDA construction uses the smul R def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L46-L46

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
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]

theorem Formalism.L2.Pj.QAt.TieLDA.smulR_def (r : R) (l : K₁ ⊗[K] U) : r • l = algebraMap R K r • l := by sorry
