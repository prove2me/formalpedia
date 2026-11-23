-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_add
-- name    : Formalism.L2.Pj.nval_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:46.836542+00:00
-- url     : https://prove2.me/theorems/c20d06eb-c4ff-4962-b878-70411a78bc57
-- title:
--   Pj: nval add
-- statement:
--   The Pj construction uses the nval add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L64-L76

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

theorem Formalism.L2.Pj.nval_add (e : ℕ) (x y : K') : min (nval V e x) (nval V e y) ≤ nval V e (x + y) := by sorry
