-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_sum_four_comm_form
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.sum_four_comm_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:48.333707+00:00
-- url     : https://prove2.me/theorems/cc874e94-32c1-4af3-94ea-f8246009fb82
-- title:
--   Column Families: sum four comm form
-- statement:
--   The Column Families construction uses the sum four comm form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L99-L105

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
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
variable {R : Type*} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.sum_four_comm_form {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by sorry
