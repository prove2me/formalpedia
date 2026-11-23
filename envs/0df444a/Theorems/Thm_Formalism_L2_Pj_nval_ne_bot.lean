-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_ne_bot
-- name    : Formalism.L2.Pj.nval_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:58.988806+00:00
-- url     : https://prove2.me/theorems/0dd71cd4-b7df-4f5b-b400-2cf59826eacd
-- title:
--   Pj: nval ne bot
-- statement:
--   The Pj construction uses the nval ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L61-L62

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable {V}
variable (V)
variable {V}

theorem Formalism.L2.Pj.nval_ne_bot (e : ℕ) (x : K') : nval V e x ≠ ⊥ := by sorry
