-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_norm_weight
-- name    : Formalism.HC.Der.Rd.log_norm_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:43.703305+00:00
-- url     : https://prove2.me/theorems/c9088069-e4f7-4d7c-83ea-00bb2c254798
-- title:
--   Rd: log norm weight
-- statement:
--   The Rd construction uses the log norm weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L251-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L251-L288

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
omit E

theorem Formalism.HC.Der.Rd.log_norm_weight (u : ZMod N) (hu : u ≠ 1) :
    Real.log |((Algebra.norm ℚ (ζ - ζ ^ u.val) : ℚ) : ℝ)| =
      (N.totient : ℝ) * (vonMangoldt (addOrderOf (u - 1)) / ((addOrderOf (u - 1)).totient : ℝ)) := by sorry
