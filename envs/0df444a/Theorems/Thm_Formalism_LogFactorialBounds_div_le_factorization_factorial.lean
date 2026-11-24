-- Prove2me | Theorems.Thm_Formalism_LogFactorialBounds_div_le_factorization_factorial
-- name    : Formalism.LogFactorialBounds.div_le_factorization_factorial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:00.225094+00:00
-- url     : https://prove2.me/theorems/193a983c-08db-4622-b89d-37fe5177c066
-- title:
--   Log Factorial Bounds: div le factorization factorial
-- statement:
--   The Log Factorial Bounds construction uses the div le factorization factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean#L10-L20

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LogFactorialBounds
open Finset Real

theorem Formalism.LogFactorialBounds.div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by sorry
