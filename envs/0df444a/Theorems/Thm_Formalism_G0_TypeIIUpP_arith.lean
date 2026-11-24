-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_arith
-- name    : Formalism.G0.TypeIIUpP.arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:17.180923+00:00
-- url     : https://prove2.me/theorems/239bf22d-a216-4322-ba98-c4363eb73dfb
-- title:
--   Type IIUp P: arith
-- statement:
--   The Type IIUp P construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L82-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L82-L133

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP

theorem Formalism.G0.TypeIIUpP.arith (q N g j ρ : ℕ) (hρ : ρ ≤ N) :
    (if ρ ≤ j then gaussBinom q (N + g - ρ) (j - ρ) else 0) =
      ∑ l ∈ Finset.range (j + 1), q ^ (l * (N + l - j)) * gaussBinom q g l *
        (if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) := by sorry
