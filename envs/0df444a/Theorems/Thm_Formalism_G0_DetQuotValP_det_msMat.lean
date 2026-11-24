-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_det_msMat
-- name    : Formalism.G0.DetQuotValP.det_msMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:34.426272+00:00
-- url     : https://prove2.me/theorems/ddf921af-41eb-417d-9f24-48a1db09cd93
-- title:
--   Det Quot Val P: det ms Mat
-- statement:
--   The Det Quot Val P construction uses the det ms Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L12-L22

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
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
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]

theorem Formalism.G0.DetQuotValP.det_msMat {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) (g : GL (Fin r) L) :
    (msMat g).det = Polynomial.X := by sorry
