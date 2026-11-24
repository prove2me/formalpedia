-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_sum_fib
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.sum_fib
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:32.643422+00:00
-- url     : https://prove2.me/theorems/8ef9dc31-7b49-4ba9-8e9f-19aaaa9d3078
-- title:
--   Unramified Trace: sum fib
-- statement:
--   The Unramified Trace construction uses the sum fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/SumFib.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/SumFib.lean#L7-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_SumFib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.sum_fib {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] (π : P → X) (V : P → ℂ) (w : X → ℂ)
    (hV : ∀ p, V p = w (π p)) :
    ∑ p, V p = ∑ x, ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by sorry
