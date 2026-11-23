-- Prove2me | Theorems.Thm_Formalism_L2_Pj_valV_ne_zero
-- name    : Formalism.L2.Pj.valV_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:11.848934+00:00
-- url     : https://prove2.me/theorems/d578fe52-c9f3-4eb4-b8a2-f4f14bdf8218
-- title:
--   Pj: val V ne zero
-- statement:
--   The Pj construction uses the val V ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L32-L33

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

theorem Formalism.L2.Pj.valV_ne_zero {x : K'} (hx : x ≠ 0) : valV V x ≠ 0 := by sorry
