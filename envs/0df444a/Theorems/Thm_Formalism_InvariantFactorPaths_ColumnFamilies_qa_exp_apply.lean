-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_exp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:34.602862+00:00
-- url     : https://prove2.me/theorems/90c582dc-9abe-4a0b-95fe-fee5c06f7f32
-- title:
--   Column Families: qa exp apply
-- statement:
--   The Column Families construction uses the qa exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L91-L95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_exp_apply {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (b p : Fin n) :
    qa_exp I (b, p) = ∑ c : ↥(TCols mu), ∑ q : Fin (colH mu c),
      if qa_row I c q = b ∧ q.val = p.val then 1 else 0 := by sorry
