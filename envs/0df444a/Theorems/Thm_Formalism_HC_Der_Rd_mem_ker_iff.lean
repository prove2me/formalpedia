-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
-- name    : Formalism.HC.Der.Rd.mem_ker_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:24.462588+00:00
-- url     : https://prove2.me/theorems/1e46be60-df4a-49b3-b369-2796a7ebbbc3
-- title:
--   Rd: mem ker iff
-- statement:
--   The Rd construction uses the mem ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L163-L166

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

theorem Formalism.HC.Der.Rd.mem_ker_iff {f : ℕ} (hf : f ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap hf).ker ↔ (u : ZMod N).val ≡ 1 [MOD f] := by sorry
