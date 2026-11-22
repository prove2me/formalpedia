-- Prove2me | Theorems.Thm_Formalism_G0_QVandermondeP_gb_eq_zero
-- name    : Formalism.G0.QVandermondeP.gb_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:01.119573+00:00
-- url     : https://prove2.me/theorems/114f8216-5f34-4443-9a9a-bde0f54a22b2
-- title:
--   QVandermonde P: gb eq zero
-- statement:
--   The QVandermonde P construction uses the gb eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L16-L22

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.QVandermondeP

theorem Formalism.G0.QVandermondeP.gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  := by sorry
