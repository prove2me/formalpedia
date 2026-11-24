-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_isUnit_of_degreeOf_eq_zero
-- name    : Formalism.G0.DetDividesP.isUnit_of_degreeOf_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:04.262518+00:00
-- url     : https://prove2.me/theorems/deb65ce7-4a5f-4fdb-b9d9-c694025a5ac9
-- title:
--   Det Divides P: is Unit of degree Of eq zero
-- statement:
--   The Det Divides P construction uses the is Unit of degree Of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L330-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L330-L337

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

theorem Formalism.G0.DetDividesP.isUnit_of_degreeOf_eq_zero {σ : Type} {p : MvPolynomial σ K} (hp : p ≠ 0)
    (h : ∀ x, degreeOf x p = 0) : IsUnit p := by sorry
