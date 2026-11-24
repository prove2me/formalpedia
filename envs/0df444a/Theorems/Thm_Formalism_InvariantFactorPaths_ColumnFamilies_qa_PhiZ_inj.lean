-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_PhiZ_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:49.541978+00:00
-- url     : https://prove2.me/theorems/34f2cb57-e5b3-49c3-bd9d-68da664da173
-- title:
--   Column Families: qa Phi Z inj
-- statement:
--   The Column Families construction uses the qa Phi Z inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L79-L80

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
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
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_inj (n : ℕ) (u : GLCoord ℤ n) (hu : IsUnit u) : Function.Injective (qa_PhiZ n u) := by sorry
