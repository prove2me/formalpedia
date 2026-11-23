-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_one_mem_KK
-- name    : Formalism.HC.Der.Rd.one_mem_KK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:49.473691+00:00
-- url     : https://prove2.me/theorems/71972565-85d5-49b9-8167-5b03d3b0a7aa
-- title:
--   Rd: one mem KK
-- statement:
--   The Rd construction uses the one mem KK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L282-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L282-L284

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

theorem Formalism.HC.Der.Rd.one_mem_KK {f : ℕ} (hf : f ∣ N) : (1 : (ZMod N)ˣ) ∈ KK N f := by sorry
