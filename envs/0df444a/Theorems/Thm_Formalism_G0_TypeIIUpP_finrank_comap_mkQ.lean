-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_finrank_comap_mkQ
-- name    : Formalism.G0.TypeIIUpP.finrank_comap_mkQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:23.132941+00:00
-- url     : https://prove2.me/theorems/9f911c31-8a14-4a0e-8096-73149489aa41
-- title:
--   Type IIUp P: finrank comap mk Q
-- statement:
--   The Type IIUp P construction uses the finrank comap mk Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L159-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L159-L187

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

theorem Formalism.G0.TypeIIUpP.finrank_comap_mkQ (A : Submodule F W) (V : Submodule F (W ⧸ A)) :
    Module.finrank F (V.comap A.mkQ) = Module.finrank F V + Module.finrank F A := by sorry
