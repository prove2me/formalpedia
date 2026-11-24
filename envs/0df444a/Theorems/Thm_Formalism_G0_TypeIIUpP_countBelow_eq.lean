-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_countBelow_eq
-- name    : Formalism.G0.TypeIIUpP.countBelow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:15.82201+00:00
-- url     : https://prove2.me/theorems/5826ff98-81ad-4454-be4a-fd7f2d70eba5
-- title:
--   Type IIUp P: count Below eq
-- statement:
--   The Type IIUp P construction uses the count Below eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L143-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L143-L157

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
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
attribute [local instance] finite_quot

theorem Formalism.G0.TypeIIUpP.countBelow_eq (A : Submodule F W) (d : ℕ) :
    countBelow A d = countBelow (⊤ : Submodule F A) d := by sorry
