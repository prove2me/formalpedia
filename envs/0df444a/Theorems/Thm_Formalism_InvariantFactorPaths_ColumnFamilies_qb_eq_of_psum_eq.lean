-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_eq_of_psum_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_eq_of_psum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:26.237804+00:00
-- url     : https://prove2.me/theorems/ef7c29ea-ab78-4dd1-a8a6-559ea3d36f75
-- title:
--   Column Families: qb eq of psum eq
-- statement:
--   The Column Families construction uses the qb eq of psum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L16-L27

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_eq_of_psum_eq {f g : Fin n → ℤ}
    (h : ∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), f b = ∑ b ∈ univ.filter (· ≤ a), g b) : f = g := by sorry
