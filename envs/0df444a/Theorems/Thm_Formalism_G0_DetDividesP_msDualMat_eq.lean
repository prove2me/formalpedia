-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_msDualMat_eq
-- name    : Formalism.G0.DetDividesP.msDualMat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:09.45682+00:00
-- url     : https://prove2.me/theorems/b0cb3baa-6622-489a-8615-feb60fcb9a04
-- title:
--   Det Divides P: ms Dual Mat eq
-- statement:
--   The Det Divides P construction uses the ms Dual Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L59-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L59-L59

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

theorem Formalism.G0.DetDividesP.msDualMat_eq (g : GL (Fin r) L) : msDualMat g = (nMat g).transpose := by sorry
