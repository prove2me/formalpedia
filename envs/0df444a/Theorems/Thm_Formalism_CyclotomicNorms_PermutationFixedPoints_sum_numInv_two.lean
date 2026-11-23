-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_sum_numInv_two
-- name    : Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:30.392473+00:00
-- url     : https://prove2.me/theorems/86d2daf7-859f-46b4-8ea2-ef99d98bf525
-- title:
--   Permutation Fixed Points: sum num Inv two
-- statement:
--   The Permutation Fixed Points construction uses the sum num Inv two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L78-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean#L78-L93

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

theorem Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv_two (N a : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0) =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) =>
          (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by sorry
