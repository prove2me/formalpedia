-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_span_inf_eq
-- name    : Formalism.L2.Pj.QAt.TieLDA.span_inf_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:26.126989+00:00
-- url     : https://prove2.me/theorems/08c84c45-ef94-4032-91fb-a43461956a13
-- title:
--   Tie LDA: span inf eq
-- statement:
--   The Tie LDA construction uses the span inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L216-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDA.lean#L216-L289

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
include hRT

theorem Formalism.L2.Pj.QAt.TieLDA.span_inf_eq (X : Submodule R U) (hX : X.FG) (W : Submodule K U) :
    Submodule.span T (Submodule.span K₁ (tm K K₁ '' (W : Set U)) : Set (K₁ ⊗[K] U)) ⊓
        Submodule.span T (tm K K₁ '' (X : Set U)) =
      Submodule.span T (tm K K₁ '' ((X ⊓ W.restrictScalars R : Submodule R U) : Set U)) := by sorry
