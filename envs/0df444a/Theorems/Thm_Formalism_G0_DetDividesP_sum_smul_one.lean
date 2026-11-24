-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_sum_smul_one
-- name    : Formalism.G0.DetDividesP.sum_smul_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:24.082799+00:00
-- url     : https://prove2.me/theorems/413f2e17-9b93-4697-9987-de66debc6e10
-- title:
--   Det Divides P: sum smul one
-- statement:
--   The Det Divides P construction uses the sum smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L183-L185

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

theorem Formalism.G0.DetDividesP.sum_smul_one {R : Type} [CommSemiring R] (t : R) (v : Fin r → R) (a : Fin r) :
    (∑ c, ((t • (1 : Matrix (Fin r) (Fin r) R)) a c) * v c) = t * v a := by sorry
