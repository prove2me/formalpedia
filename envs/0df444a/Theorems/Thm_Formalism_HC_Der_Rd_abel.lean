-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_abel
-- name    : Formalism.HC.Der.Rd.abel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:43.729949+00:00
-- url     : https://prove2.me/theorems/38efab1c-248a-4451-915a-9070a3e6d356
-- title:
--   Rd: abel
-- statement:
--   The Rd construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L200-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L200-L235

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
variable {N : ℕ} [NeZero N]
open Classical

theorem Formalism.HC.Der.Rd.abel (U : Subgroup (ZMod N)ˣ) :
    ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) =
      ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) := by sorry
