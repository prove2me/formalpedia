-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_rd
-- name    : Formalism.HC.Der.Rd.log_rd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:51.119544+00:00
-- url     : https://prove2.me/theorems/de8e31b5-a143-4818-95a3-7a8d965b5669
-- title:
--   Rd: log rd
-- statement:
--   The Rd construction uses the log rd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L292-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L292-L336

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

theorem Formalism.HC.Der.Rd.log_rd (U : Subgroup (ZMod N)ˣ)
    (hU : ∀ (σ : L ≃ₐ[ℚ] L) (u : (ZMod N)ˣ), σ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, σ (algebraMap E L x) = algebraMap E L x) ↔ u ∈ U)) :
    Real.log |(discr E : ℝ)| / Module.finrank ℚ E =
      ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by sorry
