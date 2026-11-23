-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_unitary
-- name    : Formalism.IndefR.DeterminantProjection.proj_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:18.957345+00:00
-- url     : https://prove2.me/theorems/593cc81f-6198-46cc-94eb-0be572659fcf
-- title:
--   Determinant Projection: proj unitary
-- statement:
--   The Determinant Projection construction uses the proj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L101-L104

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

theorem Formalism.IndefR.DeterminantProjection.proj_unitary (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (hainv : σ ainv = ainv) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • proj σ J u ainv).map σ)ᵀ * J * (1 + (x - 1) • proj σ J u ainv) = J := by sorry
