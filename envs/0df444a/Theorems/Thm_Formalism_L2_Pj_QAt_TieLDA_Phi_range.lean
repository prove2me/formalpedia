-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_range
-- name    : Formalism.L2.Pj.QAt.TieLDA.Phi_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:28.824504+00:00
-- url     : https://prove2.me/theorems/c0be149f-ca3a-4498-8d66-c65e2cca07b7
-- title:
--   Tie LDA: Phi range
-- statement:
--   The Tie LDA construction uses the Phi range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L81-L91

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

theorem Formalism.L2.Pj.QAt.TieLDA.Phi_range (X : Submodule R U) :
    LinearMap.range (Phi T hRT X) = Submodule.span T (tm K K₁ '' (X : Set U)) := by sorry
