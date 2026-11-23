-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_adj_Tm_ne_zero
-- name    : Formalism.G0.DetDividesP.adj_Tm_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:46.503805+00:00
-- url     : https://prove2.me/theorems/efee4404-198e-4e6f-bc5d-4993d9b998c5
-- title:
--   Det Divides P: adj Tm ne zero
-- statement:
--   The Det Divides P construction uses the adj Tm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L381-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L381-L403

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

theorem Formalism.G0.DetDividesP.adj_Tm_ne_zero (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    (Tm K A).adjugate lst l ≠ 0 := by sorry
