-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_eabH_left
-- name    : Formalism.QuantumDeterminants.ioLeft_eabH_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:45:50.568366+00:00
-- url     : https://prove2.me/theorems/a1c50263-7c28-4d70-ab26-034037dfb3fc
-- title:
--   Quantum Determinants: io Left eab H left
-- statement:
--   The Quantum Determinants construction uses the io Left eab H left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L23-L28

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

theorem Formalism.QuantumDeterminants.ioLeft_eabH_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (h : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    EabH H a b (fun x => f (h * x)) = fun x => EabH H a b f (h * x) := by sorry
