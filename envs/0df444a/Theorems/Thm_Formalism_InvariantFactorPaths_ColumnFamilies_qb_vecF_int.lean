-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_vecF_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:03.536455+00:00
-- url     : https://prove2.me/theorems/a4308f04-41fd-4eb8-8dd8-3f86f798d39b
-- title:
--   Column Families: qb vec F int
-- statement:
--   The Column Families construction uses the qb vec F int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbBasisApply.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbBasisApply.lean#L64-L66

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_vecF_int {M : GLMod n} (CF : ColFam M) : qb_vecF CF ℤ = fun x => CF.vec x.1 x.2.1 := by sorry
