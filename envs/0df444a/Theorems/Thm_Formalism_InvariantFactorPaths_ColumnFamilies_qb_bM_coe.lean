-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_bM_coe
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_bM_coe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:29.886377+00:00
-- url     : https://prove2.me/theorems/b23a9985-f6e9-4ced-83b1-92936a725e4d
-- title:
--   Column Families: qb b M coe
-- statement:
--   The Column Families construction uses the qb b M coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L63-L65

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_bM_coe (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) :
    ((qb_bM hA CF mu j : ↥(CF.MM mu)) : M.ι → ℤ) = CF.vec j.1 (canT (CF.mu j.1)) := by sorry
