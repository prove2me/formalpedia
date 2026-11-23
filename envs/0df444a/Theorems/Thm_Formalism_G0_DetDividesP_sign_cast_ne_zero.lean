-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_sign_cast_ne_zero
-- name    : Formalism.G0.DetDividesP.sign_cast_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:54.589682+00:00
-- url     : https://prove2.me/theorems/92fdd9c6-2039-4d4e-935b-1cc0ae617508
-- title:
--   Det Divides P: sign cast ne zero
-- statement:
--   The Det Divides P construction uses the sign cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L372-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L372-L373

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

theorem Formalism.G0.DetDividesP.sign_cast_ne_zero (τ : Equiv.Perm (Fin r)) : ((Equiv.Perm.sign τ : ℤ) : K) ≠ 0 := by sorry
