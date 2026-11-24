-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_diagonal_last_zero_eq
-- name    : Formalism.G0.DetDividesP.diagonal_last_zero_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:50.899627+00:00
-- url     : https://prove2.me/theorems/4651bd3c-e5a0-4e60-84c8-a7ed234c2b16
-- title:
--   Det Divides P: diagonal last zero eq
-- statement:
--   The Det Divides P construction uses the diagonal last zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L521-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L521-L527

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
variable {L : Type} [Field L]

theorem Formalism.G0.DetDividesP.diagonal_last_zero_eq (hr : 0 < r) :
    Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) =
      1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) (Pi.single (lst hr) 1) := by sorry
