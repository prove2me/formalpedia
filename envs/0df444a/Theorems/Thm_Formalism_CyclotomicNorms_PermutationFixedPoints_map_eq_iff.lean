-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_map_eq_iff
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.map_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:30.238414+00:00
-- url     : https://prove2.me/theorems/b44208e5-bb6b-4acb-9428-3d540d9dbcbf
-- title:
--   Permutation Fixed Points: map eq iff
-- statement:
--   The Permutation Fixed Points construction uses the map eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L48-L56

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.map_eq_iff {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α) :
    S.map σ.toEmbedding = S ↔ ∀ x, σ x ∈ S ↔ x ∈ S := by sorry
