-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_rho_two
-- name    : Formalism.HC.Der.Rd.rho_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:32.891298+00:00
-- url     : https://prove2.me/theorems/bab1ec20-01eb-4514-b2da-971b9ef6f9aa
-- title:
--   Rd: rho two
-- statement:
--   The Rd construction uses the rho two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L172-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L172-L290

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
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
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)

theorem Formalism.HC.Der.Rd.rho_two {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N) (hi : i ≤ e + 2)
    (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨ ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) :
    1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) ≤ rho U (2 ^ i * M) := by sorry
