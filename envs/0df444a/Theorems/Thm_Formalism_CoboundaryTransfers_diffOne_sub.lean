-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_diffOne_sub
-- name    : Formalism.CoboundaryTransfers.diffOne_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:10.982576+00:00
-- url     : https://prove2.me/theorems/97cbf493-650a-4fd3-a897-fc740f1fefd2
-- title:
--   Coboundary Transfers: diff One sub
-- statement:
--   The Coboundary Transfers construction uses the diff One sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L48-L51

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

theorem Formalism.CoboundaryTransfers.diffOne_sub (W : WachMod B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by sorry
