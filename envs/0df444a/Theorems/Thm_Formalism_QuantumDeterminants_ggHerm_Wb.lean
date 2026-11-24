-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_Wb
-- name    : Formalism.QuantumDeterminants.ggHerm_Wb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:40.10998+00:00
-- url     : https://prove2.me/theorems/d5e60dbe-d374-4410-a06a-c84a919f3286
-- title:
--   Quantum Determinants: gg Herm Wb
-- statement:
--   The Quantum Determinants construction uses the gg Herm Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L210-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L210-L222

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.ggHerm_Wb (k r : ℕ) (z w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) w z =
      (∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩, star (z i) * w i) -
        star (z ⟨r + k, by omega⟩) * w ⟨r + k, by omega⟩ := by sorry
