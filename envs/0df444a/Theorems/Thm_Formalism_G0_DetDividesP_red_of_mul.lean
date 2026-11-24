-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_red_of_mul
-- name    : Formalism.G0.DetDividesP.red_of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:35.854808+00:00
-- url     : https://prove2.me/theorems/da5ecb93-23c6-4167-a80a-5c1672a1ee29
-- title:
--   Det Divides P: red of mul
-- statement:
--   The Det Divides P construction uses the red of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L115-L121

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

theorem Formalism.G0.DetDividesP.red_of_mul (hr : 0 < r) (A : Fin r → ι) (G' : MvPolynomial (ι × Fin r) K) (n : ℕ)
    (h : Red A (detLetters (K := K) A * G') (n + 1)) : Red A G' n := by sorry
