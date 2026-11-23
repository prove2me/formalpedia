-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_hsq_map
-- name    : Formalism.IndefR.DeterminantProjection.hsq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:17.699592+00:00
-- url     : https://prove2.me/theorems/61f80990-44ca-41d3-b90a-da59d3c3acbc
-- title:
--   Determinant Projection: hsq map
-- statement:
--   The Determinant Projection construction uses the hsq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L118-L121

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.IndefR.DeterminantProjection.hsq_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) :
    f (hsq σ J u) = hsq σ' (J.map f) (fun i => f (u i)) := by sorry
