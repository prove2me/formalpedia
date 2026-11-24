-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_unitary_of_proj
-- name    : Formalism.IndefR.DeterminantProjection.unitary_of_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:56.409665+00:00
-- url     : https://prove2.me/theorems/0a1c2e47-f63b-4e5a-afaa-770a7a519a9d
-- title:
--   Determinant Projection: unitary of proj
-- statement:
--   The Determinant Projection construction uses the unitary of proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L13-L30

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

theorem Formalism.IndefR.DeterminantProjection.unitary_of_proj (σ : A →+* A) (J R : Matrix n n A) (hRR : R * R = R)
    (hJR : J * R = (R.map σ)ᵀ * J) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • R).map σ)ᵀ * J * (1 + (x - 1) • R) = J := by sorry
