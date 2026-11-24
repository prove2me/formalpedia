-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_foldr
-- name    : Formalism.QuantumDeterminants.ioh_foldr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:51.440493+00:00
-- url     : https://prove2.me/theorems/6823ee34-0130-41ce-be6b-f1781f14ff63
-- title:
--   Quantum Determinants: ioh foldr
-- statement:
--   The Quantum Determinants construction uses the ioh foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L269-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L269-L281

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

theorem Formalism.QuantumDeterminants.ioh_foldr (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (l : List (ℂ × Fin n × Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (l.map fun p => Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) G =
      fun x => (l.map fun p => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) p.1 p.2.1 p.2.2).foldr
        (fun T h => T h) (fun y => G (Q * y * P)) (P * x * Q) := by sorry
