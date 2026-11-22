-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prod_single
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_prod_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:14.719695+00:00
-- url     : https://prove2.me/theorems/b46402be-6f90-4de8-8b52-ba78a6e77672
-- title:
--   Column Families: qb prod single
-- statement:
--   The Column Families construction uses the qb prod single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L67-L72

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_prod_single {κ G : Type*} [AddCommMonoid G] (s : Finset κ) (f : κ → G) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : ℤ)) = AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by sorry
