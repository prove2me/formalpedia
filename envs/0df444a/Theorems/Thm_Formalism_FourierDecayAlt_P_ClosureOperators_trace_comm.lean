-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_trace_comm
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.trace_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:32.258699+00:00
-- url     : https://prove2.me/theorems/dcc37fd2-79eb-442d-a77f-6fea9f148043
-- title:
--   Closure Operators: trace comm
-- statement:
--   The Closure Operators construction uses the trace comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L155-L159

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.ClosureOperators.trace_comm {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (a b : Fin N) :
    (∑ c, E c c) * E a b = E a b * ∑ c, E c c := by sorry
