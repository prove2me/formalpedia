-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_smooth
-- name    : Formalism.QuantumDeterminants.ioh_smooth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:44.580688+00:00
-- url     : https://prove2.me/theorems/c230f417-51b4-4caf-b213-0400cd8546d4
-- title:
--   Quantum Determinants: ioh smooth
-- statement:
--   The Quantum Determinants construction uses the ioh smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L114-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L114-L128

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

theorem Formalism.QuantumDeterminants.ioh_smooth (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hf : SmoothOnH H f) : SmoothOnGV ε (fun x => f (Q * x * P)) := by sorry
