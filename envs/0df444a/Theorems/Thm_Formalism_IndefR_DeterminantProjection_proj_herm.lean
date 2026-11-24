-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_proj_herm
-- name    : Formalism.IndefR.DeterminantProjection.proj_herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:11.618427+00:00
-- url     : https://prove2.me/theorems/3350fc33-170d-42f4-bbab-8736bae528e3
-- title:
--   Determinant Projection: proj herm
-- statement:
--   The Determinant Projection construction uses the proj herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L84-L99

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

theorem Formalism.IndefR.DeterminantProjection.proj_herm (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (hainv : σ ainv = ainv) :
    J * proj σ J u ainv = ((proj σ J u ainv).map σ)ᵀ * J := by sorry
