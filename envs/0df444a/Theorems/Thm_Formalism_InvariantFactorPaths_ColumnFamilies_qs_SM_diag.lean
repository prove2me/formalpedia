-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_diag
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:26.130618+00:00
-- url     : https://prove2.me/theorems/ebd645b1-822e-45c4-be41-e5116e0923ed
-- title:
--   Column Families: qs SM diag
-- statement:
--   The Column Families construction uses the qs SM diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L93-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L93-L121

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_diag {A : Type*} [CommRing A] (d : Fin n → A) (b : ℕ) (α β : SymIdx n b) :
    qs_SM (Matrix.diagonal d) b α β = if α = β then ∏ x, d x ^ (β.1 x : ℕ) else 0 := by sorry
