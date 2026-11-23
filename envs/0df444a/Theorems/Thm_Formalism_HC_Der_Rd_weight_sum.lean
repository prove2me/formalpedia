-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_weight_sum
-- name    : Formalism.HC.Der.Rd.weight_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:42.939719+00:00
-- url     : https://prove2.me/theorems/08b298ae-ffd4-4f92-abfd-e9feb07553f1
-- title:
--   Rd: weight sum
-- statement:
--   The Rd construction uses the weight sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L45-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L45-L127

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd

theorem Formalism.HC.Der.Rd.weight_sum {N m : ℕ} (hN : N ≠ 0) (hm : m ∣ N) (hm1 : m ≠ 1) :
    ∑ m' ∈ N.divisors.filter (fun m' => m ∣ m'), vonMangoldt m' * ((N / m').totient : ℝ) =
      (N.totient : ℝ) * (vonMangoldt m / (m.totient : ℝ)) := by sorry
