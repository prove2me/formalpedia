-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
-- name    : Formalism.QuantumDeterminants.ioh_inUJ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:00.663647+00:00
-- url     : https://prove2.me/theorems/483db513-36c5-405e-ac08-3e0c12ccdf3e
-- title:
--   Quantum Determinants: ioh in UJ
-- statement:
--   The Quantum Determinants construction uses the ioh in UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L90-L98

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

theorem Formalism.QuantumDeterminants.ioh_inUJ (ε : Fin n → Bool) (H P Q g : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hg : inUH H g) : inUJ ε (P * g * Q) := by sorry
