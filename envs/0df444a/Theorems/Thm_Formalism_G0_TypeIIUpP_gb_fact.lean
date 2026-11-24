-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_gb_fact
-- name    : Formalism.G0.TypeIIUpP.gb_fact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:18.356839+00:00
-- url     : https://prove2.me/theorems/d68fc04d-e8d9-4d35-84f1-c477138b7f2d
-- title:
--   Type IIUp P: gb fact
-- statement:
--   The Type IIUp P construction uses the gb fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L38-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L38-L71

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

theorem Formalism.G0.TypeIIUpP.gb_fact (q : ℕ) : ∀ n k : ℕ, k ≤ n →
    gaussBinom q n k * qfact q k * qfact q (n - k) = qfact q n
  := by sorry
