-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_conj_diagonal_last_zero
-- name    : Formalism.G0.DetDividesP.conj_diagonal_last_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:52.68769+00:00
-- url     : https://prove2.me/theorems/014011fb-9e7e-4f10-b65a-9da91359b405
-- title:
--   Det Divides P: conj diagonal last zero
-- statement:
--   The Det Divides P construction uses the conj diagonal last zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L563-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L563-L567

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

theorem Formalism.G0.DetDividesP.conj_diagonal_last_zero (hr : 0 < r) (φ : Fin r → L) (hφ : φ (lst hr) = 1) :
    (gU (lst hr) φ hφ).1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) *
      (gU (lst hr) φ hφ)⁻¹.1 = 1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ := by sorry
