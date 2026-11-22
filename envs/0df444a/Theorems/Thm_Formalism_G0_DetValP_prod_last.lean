-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_prod_last
-- name    : Formalism.G0.DetValP.prod_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:17.240799+00:00
-- url     : https://prove2.me/theorems/ddb82ee8-9c10-4bab-a8c5-ff96c4e421ae
-- title:
--   Det Val P: prod last
-- statement:
--   The Det Val P construction uses the prod last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L50-L58

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

theorem Formalism.G0.DetValP.prod_last {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) :
    ∏ a : Fin r, (if a.val + 1 = r then (Polynomial.X : Polynomial L) else 1) = Polynomial.X := by sorry
