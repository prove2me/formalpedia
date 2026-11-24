-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_ptA_det
-- name    : Formalism.G0.DetDividesP.aeval_ptA_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:48.935805+00:00
-- url     : https://prove2.me/theorems/eaeca4a5-d8d3-4bcc-8a06-fa02ffbdf918
-- title:
--   Det Divides P: aeval pt A det
-- statement:
--   The Det Divides P construction uses the aeval pt A det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L103-L113

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

theorem Formalism.G0.DetDividesP.aeval_ptA_det (hr : 0 < r) {L : Type} [Field L] [Algebra K L] (A : Fin r → ι) (g : GL (Fin r) L)
    (x : ι × Fin r → L) :
    MvPolynomial.aeval (ptA A g x) (detLetters (K := K) A) =
      C (MvPolynomial.aeval x (detLetters (K := K) A)) * X := by sorry
