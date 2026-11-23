-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_I_actMat
-- name    : Formalism.L2.DIV.CSD.I_actMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:10.769817+00:00
-- url     : https://prove2.me/theorems/05ec1dc1-ff7d-4233-9707-e86181293940
-- title:
--   CSD: I act Mat
-- statement:
--   The CSD construction uses the I act Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L81-L89

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

theorem Formalism.L2.DIV.CSD.I_actMat (t : G) (x : Fin S.dim → K) :
    S.I ((S.actMat r t).mulVec x) = (r t (S.basis.equivFun.symm x) : S.Cl → S.V) := by sorry
