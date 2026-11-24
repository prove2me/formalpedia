-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_Top
-- name    : Formalism.QuantumDeterminants.ioh_Top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:56.950267+00:00
-- url     : https://prove2.me/theorems/cf604660-6174-4f88-8234-b1d772ac2e3a
-- title:
--   Quantum Determinants: ioh Top
-- statement:
--   The Quantum Determinants construction uses the ioh Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L257-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L257-L267

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

theorem Formalism.QuantumDeterminants.ioh_Top (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (u : ℂ) (a b : Fin n)
    (R : Matrix (Fin n) (Fin n) ℂ → E) :
    Top (EabH H) u a b (fun x => R (P * x * Q)) =
      fun x => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) u a b R (P * x * Q) := by sorry
