-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_rdV_left
-- name    : Formalism.QuantumDeterminants.ioLeft_rdV_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:44:17.323854+00:00
-- url     : https://prove2.me/theorems/497e8bce-862d-48b1-b516-b66ef2d4662a
-- title:
--   Quantum Determinants: io Left rd V left
-- statement:
--   The Quantum Determinants construction uses the io Left rd V left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L11-L15

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.QuantumDeterminants.ioLeft_rdV_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X h : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    RdV X (fun x => f (h * x)) = fun x => RdV X f (h * x) := by sorry
