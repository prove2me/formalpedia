-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_supp_in
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:05.229803+00:00
-- url     : https://prove2.me/theorems/b6db0c70-914b-4a67-809d-56e6d65c17f9
-- title:
--   Column Families: qb supp in
-- statement:
--   The Column Families construction uses the qb supp in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L147-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QbIndepField.lean#L147-L161

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_supp_in (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu (∑ x, a x • qb_vecF CF F x) = 0) :
    ∀ x, a x ≠ 0 → CF.mu x.1 ∈ pi := by sorry
