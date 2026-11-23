-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_mul
-- name    : Formalism.L2.Pj.nval_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:37.769793+00:00
-- url     : https://prove2.me/theorems/662438c3-3dcc-43d9-8ff9-c7540640f9cf
-- title:
--   Pj: nval mul
-- statement:
--   The Pj construction uses the nval mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L78-L84

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

theorem Formalism.L2.Pj.nval_mul (e : ℕ) (x y : K') : nval V e (x * y) = nval V e x + nval V e y := by sorry
