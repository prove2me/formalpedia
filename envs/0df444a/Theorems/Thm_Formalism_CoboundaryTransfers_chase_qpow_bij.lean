-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_chase_qpow_bij
-- name    : Formalism.CoboundaryTransfers.chase_qpow_bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:56.509173+00:00
-- url     : https://prove2.me/theorems/a2c0728a-fe6e-41ea-9907-6a7dc5b5a29a
-- title:
--   Coboundary Transfers: chase qpow bij
-- statement:
--   The Coboundary Transfers construction uses the chase qpow bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DiffOneSmulOfTower.lean#L12-L23

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

theorem Formalism.CoboundaryTransfers.chase_qpow_bij (W : WachMod B M D) (j : ℕ) :
    Function.Bijective (fun x : D => B.Q ^ j • x) := by sorry
