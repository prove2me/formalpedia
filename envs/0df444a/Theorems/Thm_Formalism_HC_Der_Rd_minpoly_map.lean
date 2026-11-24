-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_minpoly_map
-- name    : Formalism.HC.Der.Rd.minpoly_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:46.419919+00:00
-- url     : https://prove2.me/theorems/a24a84a8-cd02-489c-8ee4-cb37eac9c61b
-- title:
--   Rd: minpoly map
-- statement:
--   The Rd construction uses the minpoly map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L105-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L105-L131

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

theorem Formalism.HC.Der.Rd.minpoly_map : (minpoly E ζ).map (algebraMap E L) = Lagrange.nodal Finset.univ fun σ : L ≃ₐ[E] L => σ ζ := by sorry
