-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_bc
-- name    : Formalism.L2.Pj.nval_bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:23.515172+00:00
-- url     : https://prove2.me/theorems/166407f4-7028-488b-b761-6cd7e928c24c
-- title:
--   Pj: nval bc
-- statement:
--   The Pj construction uses the nval bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L90-L98

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

theorem Formalism.L2.Pj.nval_bc {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (i : K' →+* K'') {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) (e : ℕ) (x : K') :
    nval V' (r * e) (i x) = nval V e x := by sorry
