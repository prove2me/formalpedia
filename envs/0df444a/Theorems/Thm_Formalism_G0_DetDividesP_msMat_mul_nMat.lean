-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_msMat_mul_nMat
-- name    : Formalism.G0.DetDividesP.msMat_mul_nMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:54.674715+00:00
-- url     : https://prove2.me/theorems/14be38a7-136f-481a-9454-46c4c1ba808c
-- title:
--   Det Divides P: ms Mat mul n Mat
-- statement:
--   The Det Divides P construction uses the ms Mat mul n Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L38-L57

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}

theorem Formalism.G0.DetDividesP.msMat_mul_nMat (g : GL (Fin r) L) : msMat g * nMat g = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by sorry
