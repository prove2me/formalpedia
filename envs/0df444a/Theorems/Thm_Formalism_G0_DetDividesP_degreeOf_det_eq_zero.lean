-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_degreeOf_det_eq_zero
-- name    : Formalism.G0.DetDividesP.degreeOf_det_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:01.954832+00:00
-- url     : https://prove2.me/theorems/c2fef3b8-1fcd-45ba-83f4-bf773298c211
-- title:
--   Det Divides P: degree Of det eq zero
-- statement:
--   The Det Divides P construction uses the degree Of det eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L320-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L320-L328

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

theorem Formalism.G0.DetDividesP.degreeOf_det_eq_zero {σ : Type} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (x : σ)
    (h : ∀ i j, degreeOf x (M i j) = 0) : degreeOf x M.det = 0 := by sorry
