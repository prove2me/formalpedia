-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_rank_one_conj_eq
-- name    : Formalism.G0.DetDividesP.rank_one_conj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:12.835805+00:00
-- url     : https://prove2.me/theorems/0e8f33e4-cbde-4b94-bd4f-1863a93823fd
-- title:
--   Det Divides P: rank one conj eq
-- statement:
--   The Det Divides P construction uses the rank one conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L529-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L529-L548

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

theorem Formalism.G0.DetDividesP.rank_one_conj_eq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)) *
      (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (Pi.single i 1)) *
      (1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1))
      = 1 - Matrix.vecMulVec (Pi.single i (1 : L)) φ := by sorry
