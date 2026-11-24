-- Prove2me | Theorems.Thm_Formalism_IndefR_DeterminantProjection_exists_aniso
-- name    : Formalism.IndefR.DeterminantProjection.exists_aniso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:01.486148+00:00
-- url     : https://prove2.me/theorems/bfb615d9-e370-43d7-a7da-e4c07782af04
-- title:
--   Determinant Projection: exists aniso
-- statement:
--   The Determinant Projection construction uses the exists aniso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L129-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L129-L170

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
variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.IndefR.DeterminantProjection.exists_aniso (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n K) (hJ : ∀ i j, σ (J i j) = J j i)
    (hdet : J.det ≠ 0) [Nonempty n] : ∃ u : n → K, hsq σ J u ≠ 0 := by sorry
