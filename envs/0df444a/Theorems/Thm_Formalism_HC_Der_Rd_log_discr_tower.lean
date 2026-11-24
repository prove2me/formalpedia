-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_discr_tower
-- name    : Formalism.HC.Der.Rd.log_discr_tower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:05.271259+00:00
-- url     : https://prove2.me/theorems/07287c77-9a9e-4c4f-988e-3396f4c7e6dd
-- title:
--   Rd: log discr tower
-- statement:
--   The Rd construction uses the log discr tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L185-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L185-L209

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
open Classical

theorem Formalism.HC.Der.Rd.log_discr_tower : Real.log |(discr L : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      Module.finrank E L * Real.log |(discr E : ℝ)| := by sorry
