-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_collapse
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_collapse
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:50.004271+00:00
-- url     : https://prove2.me/theorems/d9721139-f773-4f76-83d1-003d2741c3c1
-- title:
--   Column Families: qs collapse
-- statement:
--   The Column Families construction uses the qs collapse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHHigh.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHHigh.lean#L52-L65

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_collapse {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) (P : Prop) [Decidable P]
    (F : ℤ → Finset (Fin n)) (hF : P → ∀ c, (F c).card = colH mu c) (f : (ℤ → Finset (Fin n)) → M)
    [∀ I : TIdx mu, Decidable (P ∧ qs_ext mu I = F)] :
    ∑ I : TIdx mu, (if P ∧ qs_ext mu I = F then f (qs_ext mu I) else 0) = if P then f F else 0 := by sorry
