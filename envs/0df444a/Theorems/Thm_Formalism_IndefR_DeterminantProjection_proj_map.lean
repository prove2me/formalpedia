-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_map
-- name    : Formalism.IndefR.DeterminantProjection.proj_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:51.931519+00:00
-- url     : https://prove2.me/theorems/7d7b92a7-3324-52e3-b436-10a5a0b4b3eb
-- title:
--   Determinant Projection: proj map
-- statement:
--   The Determinant Projection construction uses the proj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L111-L116

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

theorem Formalism.IndefR.DeterminantProjection.proj_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (ainv : A) :
    (proj σ J u ainv).map f = proj σ' (J.map f) (fun i => f (u i)) (f ainv) := by sorry
