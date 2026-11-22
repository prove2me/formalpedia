-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_TMat_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:37.353521+00:00
-- url     : https://prove2.me/theorems/f234b3f1-ce77-4f51-b02f-dcb2f846a322
-- title:
--   Column Families: qs TMat eq
-- statement:
--   The Column Families construction uses the qs TMat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHHigh.lean#L99-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHHigh.lean#L99-L129

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_TMat_eq {mu : Fin n → ℤ} (hmu : Dominant mu) (lo hi : ℤ) (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ hi)
    (J I : TIdx mu) : TMat mu J I = qs_TM lo (Finset.Ioc lo hi) (qs_ext mu J) (qs_ext mu I) := by sorry
