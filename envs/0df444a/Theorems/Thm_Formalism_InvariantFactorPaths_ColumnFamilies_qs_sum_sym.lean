-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_sym
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_sym
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:23.171895+00:00
-- url     : https://prove2.me/theorems/438f122b-0e70-4c4b-80e7-7c591ba94545
-- title:
--   Column Families: qs sum sym
-- statement:
--   The Column Families construction uses the qs sum sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L55-L69

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_sym {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) {b : ℕ}
    (hb : Fintype.card ι = b) (m : ι → Fin n) (α : SymIdx n b) (r : A) :
    ∑ β : SymIdx n b, qs_SM G b α β * (if (∀ x, qs_cnt m x = (β.1 x : ℕ)) then r else 0) =
      (∑ a : ι → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then ∏ c, G (a c) (m c) else 0) * r := by sorry
