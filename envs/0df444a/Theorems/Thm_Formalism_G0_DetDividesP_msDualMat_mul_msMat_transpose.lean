-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_msDualMat_mul_msMat_transpose
-- name    : Formalism.G0.DetDividesP.msDualMat_mul_msMat_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:04.462862+00:00
-- url     : https://prove2.me/theorems/3a01a5a2-02e0-469c-acf7-6eb3629f5144
-- title:
--   Det Divides P: ms Dual Mat mul ms Mat transpose
-- statement:
--   The Det Divides P construction uses the ms Dual Mat mul ms Mat transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L61-L63

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

theorem Formalism.G0.DetDividesP.msDualMat_mul_msMat_transpose (g : GL (Fin r) L) :
    msDualMat g * (msMat g).transpose = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by sorry
