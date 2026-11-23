-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_actMat_mul_inv
-- name    : Formalism.L2.DIV.CSD.actMat_mul_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:25.065862+00:00
-- url     : https://prove2.me/theorems/735be57e-d9b1-48e3-b6eb-ebbaf8daa312
-- title:
--   CSD: act Mat mul inv
-- statement:
--   The CSD construction uses the act Mat mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L197-L200

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Formalism.L2.DIV.CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem Formalism.L2.DIV.CSD.actMat_mul_inv (t : G) : S.actMat r t * S.actMat r t⁻¹ = 1 := by sorry
