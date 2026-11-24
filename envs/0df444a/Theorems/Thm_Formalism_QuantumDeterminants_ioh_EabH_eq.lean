-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq
-- name    : Formalism.QuantumDeterminants.ioh_EabH_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:59.821988+00:00
-- url     : https://prove2.me/theorems/8a69727d-4e47-4db2-bde1-491ca73a5550
-- title:
--   Quantum Determinants: ioh Eab H eq
-- statement:
--   The Quantum Determinants construction uses the ioh Eab H eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L71-L77

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.ioh_EabH_eq (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (x : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b f x = EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) (P * x * Q) := by sorry
