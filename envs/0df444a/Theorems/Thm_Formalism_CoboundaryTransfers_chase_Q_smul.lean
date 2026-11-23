-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_smul
-- name    : Formalism.CoboundaryTransfers.chase_Q_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:01.814698+00:00
-- url     : https://prove2.me/theorems/239346ae-124d-43e6-80db-4cb97dac9e7e
-- title:
--   Coboundary Transfers: chase Q smul
-- statement:
--   The Coboundary Transfers construction uses the chase Q smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L30-L33

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

theorem Formalism.CoboundaryTransfers.chase_Q_smul (W : WachMod B M D) (r : O) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by sorry
