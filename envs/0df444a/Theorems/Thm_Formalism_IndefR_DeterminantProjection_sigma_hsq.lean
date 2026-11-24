-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_sigma_hsq
-- name    : Formalism.IndefR.DeterminantProjection.sigma_hsq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:10.435525+00:00
-- url     : https://prove2.me/theorems/ae278b6b-d389-4d50-9a4d-c93e80f6ac6d
-- title:
--   Determinant Projection: sigma hsq
-- statement:
--   The Determinant Projection construction uses the sigma hsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L66-L74

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

theorem Formalism.IndefR.DeterminantProjection.sigma_hsq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) : σ (hsq σ J u) = hsq σ J u := by sorry
