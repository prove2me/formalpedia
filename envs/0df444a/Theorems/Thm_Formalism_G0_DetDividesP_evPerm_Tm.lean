-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_evPerm_Tm
-- name    : Formalism.G0.DetDividesP.evPerm_Tm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:09.169675+00:00
-- url     : https://prove2.me/theorems/e23b09c7-81a0-42bf-8335-c84c651e19f2
-- title:
--   Det Divides P: ev Perm Tm
-- statement:
--   The Det Divides P construction uses the ev Perm Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L363-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L363-L370

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

theorem Formalism.G0.DetDividesP.evPerm_Tm (A : Fin r → ι) (hA : Function.Injective A) (τ : Equiv.Perm (Fin r)) :
    (evPerm (K := K) A τ).mapMatrix (Tm K A) = τ.permMatrix K := by sorry
