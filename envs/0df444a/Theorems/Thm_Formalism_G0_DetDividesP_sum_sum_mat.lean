-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_sum_sum_mat
-- name    : Formalism.G0.DetDividesP.sum_sum_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:15.689652+00:00
-- url     : https://prove2.me/theorems/009eae51-a707-4368-8a40-455c091954ae
-- title:
--   Det Divides P: sum sum mat
-- statement:
--   The Det Divides P construction uses the sum sum mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L178-L181

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
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.sum_sum_mat {R : Type} [CommSemiring R] (M N : Matrix (Fin r) (Fin r) R) (v : Fin r → R) (a : Fin r) :
    (∑ b, M a b * ∑ c, N b c * v c) = ∑ c, (M * N) a c * v c := by sorry
