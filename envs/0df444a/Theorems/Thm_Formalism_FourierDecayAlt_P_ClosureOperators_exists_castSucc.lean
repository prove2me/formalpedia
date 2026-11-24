-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_exists_castSucc
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.exists_castSucc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:49:21.548943+00:00
-- url     : https://prove2.me/theorems/ab46ec2c-5209-4510-865d-cf16874776c2
-- title:
--   Closure Operators: exists cast Succ
-- statement:
--   The Closure Operators construction uses the exists cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L144-L147

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

theorem Formalism.FourierDecayAlt.P.ClosureOperators.exists_castSucc {n : ℕ} (a : Fin (n + 1)) (h : a ≠ Fin.last n) : ∃ a' : Fin n, a = a'.castSucc := by sorry
