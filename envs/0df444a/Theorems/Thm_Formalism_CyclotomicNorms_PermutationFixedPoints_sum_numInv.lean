-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_sum_numInv
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:30.415272+00:00
-- url     : https://prove2.me/theorems/4985d6f5-b87e-4342-898e-0e65f415bd54
-- title:
--   Permutation Fixed Points: sum num Inv
-- statement:
--   The Permutation Fixed Points construction uses the sum num Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L71-L76

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv (N a : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), numInv N a σ =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card := by sorry
