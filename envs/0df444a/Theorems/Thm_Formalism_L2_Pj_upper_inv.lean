-- Prove2me | Theorems.Thm_Formalism_L2_Pj_upper_inv
-- name    : Formalism.L2.Pj.upper_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:49.699657+00:00
-- url     : https://prove2.me/theorems/8a5e7723-44bd-4889-a3bd-1375dbba560c
-- title:
--   Pj: upper inv
-- statement:
--   The Pj construction uses the upper inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L140-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean#L140-L159

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

theorem Formalism.L2.Pj.upper_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by sorry
