-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_sum_totient_pow
-- name    : Formalism.HC.Der.Rd.sum_totient_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:56.686691+00:00
-- url     : https://prove2.me/theorems/80bff491-a53c-48ee-a56c-c3af3f1728b3
-- title:
--   Rd: sum totient pow
-- statement:
--   The Rd construction uses the sum totient pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L9-L16

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

theorem Formalism.HC.Der.Rd.sum_totient_pow {l : ℕ} (hl : l.Prime) (s : ℕ) : ∑ k ∈ range (s + 1), (l ^ k).totient = l ^ s := by sorry
