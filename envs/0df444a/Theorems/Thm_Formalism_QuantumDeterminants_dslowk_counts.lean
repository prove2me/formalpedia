-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_dslowk_counts
-- name    : Formalism.QuantumDeterminants.dslowk_counts
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:38.655245+00:00
-- url     : https://prove2.me/theorems/d9aa276d-fd5d-46e3-8ca5-ca3c0a898c1b
-- title:
--   Quantum Determinants: dslowk counts
-- statement:
--   The Quantum Determinants construction uses the dslowk counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L56-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L56-L107

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL

theorem Formalism.QuantumDeterminants.dslowk_counts {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => a < c ∧ ε c = ε a).card =
        (univ.filter fun c => b < c ∧ ε c = ε b).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => c < b ∧ ε c = ε b).card =
        (univ.filter fun c => c < a ∧ ε c = ε a).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + ncBetween ε a b + 1 + (a : ℕ) =
        (b : ℕ) := by sorry
