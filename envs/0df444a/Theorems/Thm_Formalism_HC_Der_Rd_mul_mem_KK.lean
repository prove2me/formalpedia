-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_mul_mem_KK
-- name    : Formalism.HC.Der.Rd.mul_mem_KK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:21.345547+00:00
-- url     : https://prove2.me/theorems/466f935b-999e-4c5f-aa42-f5945cfe4b84
-- title:
--   Rd: mul mem KK
-- statement:
--   The Rd construction uses the mul mem KK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L286-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L286-L288

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

theorem Formalism.HC.Der.Rd.mul_mem_KK {f : ℕ} (hf : f ∣ N) {u v : (ZMod N)ˣ} (hu : u ∈ KK N f) (hv : v ∈ KK N f) : u * v ∈ KK N f := by sorry
