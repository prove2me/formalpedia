-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_detLetters
-- name    : Formalism.G0.DetDividesP.aeval_detLetters
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:54.004023+00:00
-- url     : https://prove2.me/theorems/59c617c3-d766-484d-ad57-4a0af3e6f6a7
-- title:
--   Det Divides P: aeval det Letters
-- statement:
--   The Det Divides P construction uses the aeval det Letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L98-L101

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

theorem Formalism.G0.DetDividesP.aeval_detLetters {B : Type} [CommRing B] [Algebra K B] (A : Fin r → ι) (y : ι × Fin r → B) :
    MvPolynomial.aeval y (detLetters (K := K) A) = (Matrix.of fun l a => y (A l, a)).det := by sorry
