-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_isTorsionFree_sub
-- name    : Formalism.L2.Pj.QAt.TieLDA.isTorsionFree_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:36:56.135474+00:00
-- url     : https://prove2.me/theorems/6ad90083-1648-4714-b40f-46a73555c567
-- title:
--   Tie LDA: is Torsion Free sub
-- statement:
--   The Tie LDA construction uses the is Torsion Free sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L117-L125

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
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
include K

theorem Formalism.L2.Pj.QAt.TieLDA.isTorsionFree_sub (X : Submodule R U) : Module.IsTorsionFree R X := by sorry
