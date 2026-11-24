-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_sum_mid
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.sum_mid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:07.076354+00:00
-- url     : https://prove2.me/theorems/58bd374a-9b82-4ffa-bb24-2923dcb033e1
-- title:
--   Bruhat Big Cell: sum mid
-- statement:
--   The Bruhat Big Cell construction uses the sum mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L104-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L104-L119

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem Formalism.QuantumDeterminants.BruhatBigCell.sum_mid (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) → f p = 0) :
    ∑ p, f p = ∑ q : Fin (k + 1), f (wI k r q) := by sorry
