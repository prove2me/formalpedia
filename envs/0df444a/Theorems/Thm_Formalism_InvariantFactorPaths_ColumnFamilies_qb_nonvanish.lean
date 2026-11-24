-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_nonvanish
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_nonvanish
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:52.369181+00:00
-- url     : https://prove2.me/theorems/1d5cb574-f62d-4224-8348-98ea7b354867
-- title:
--   Column Families: qb nonvanish
-- statement:
--   The Column Families construction uses the qb nonvanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L114-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L114-L145

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
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
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_nonvanish (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (nu : Fin n → ℤ) (hmax : ∀ x, a x ≠ 0 → DomLE nu (CF.mu x.1) → CF.mu x.1 = nu)
    (h0 : qb_ev M F nu (∑ x, a x • qb_vecF CF F x) = 0) : ∀ x, CF.mu x.1 = nu → a x = 0 := by sorry
