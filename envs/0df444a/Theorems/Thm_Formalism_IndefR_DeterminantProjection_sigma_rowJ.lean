-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_sigma_rowJ
-- name    : Formalism.IndefR.DeterminantProjection.sigma_rowJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:42.912013+00:00
-- url     : https://prove2.me/theorems/11451184-1ad6-4dc6-854a-8acb9afd4a70
-- title:
--   Determinant Projection: sigma row J
-- statement:
--   The Determinant Projection construction uses the sigma row J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L61-L64

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

theorem Formalism.IndefR.DeterminantProjection.sigma_rowJ (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (i : n) : σ (rowJ σ J u i) = (J *ᵥ u) i := by sorry
