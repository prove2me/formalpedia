-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_sub
-- name    : Formalism.CoboundaryTransfers.chase_Q_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:03.844799+00:00
-- url     : https://prove2.me/theorems/3dab71cb-18e5-4cba-8c13-704552fc57a1
-- title:
--   Coboundary Transfers: chase Q sub
-- statement:
--   The Coboundary Transfers construction uses the chase Q sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L25-L29

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

theorem Formalism.CoboundaryTransfers.chase_Q_sub (W : WachMod B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) :
    W.QInv (x - y) := by sorry
