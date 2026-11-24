-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_msMat_one
-- name    : Formalism.G0.DetValP.msMat_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:03.093839+00:00
-- url     : https://prove2.me/theorems/70e57b75-1700-45b7-aad1-6b786b75ff67
-- title:
--   Det Val P: ms Mat one
-- statement:
--   The Det Val P construction uses the ms Mat one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L38-L41

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
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
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]

theorem Formalism.G0.DetValP.msMat_one {L : Type} [Field L] {r : ℕ} :
    msMat (1 : GL (Fin r) L) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by sorry
