-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_msMat_eval_zero_mul_eq_mul_diagonal
-- name    : Formalism.G0.DetQuotValP.msMat_eval_zero_mul_eq_mul_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:19.117469+00:00
-- url     : https://prove2.me/theorems/5e0397ec-75a6-4a51-a467-c437c31a87f9
-- title:
--   Det Quot Val P: ms Mat eval zero mul eq mul diagonal
-- statement:
--   The Det Quot Val P construction uses the ms Mat eval zero mul eq mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L71-L88

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

theorem Formalism.G0.DetQuotValP.msMat_eval_zero_mul_eq_mul_diagonal {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom (0 : L)) * g.1 =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by sorry
