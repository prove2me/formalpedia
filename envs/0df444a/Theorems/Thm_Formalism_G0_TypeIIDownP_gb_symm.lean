-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIDownP_gb_symm
-- name    : Formalism.G0.TypeIIDownP.gb_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:26.419895+00:00
-- url     : https://prove2.me/theorems/93a2c54d-b665-437d-bb3b-7cb6d6e0c498
-- title:
--   Type IIDown P: gb symm
-- statement:
--   The Type IIDown P construction uses the gb symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L107-L121

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP

theorem Formalism.G0.TypeIIDownP.gb_symm (q : ℕ) : ∀ a b : ℕ, gaussBinom q (a + b) a = gaussBinom q (a + b) b
  := by sorry
