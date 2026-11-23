-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_eq_lift
-- name    : Formalism.L2.DIV.CSD.gaMat_eq_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:04.654812+00:00
-- url     : https://prove2.me/theorems/8f9e86b7-1c3c-4729-b603-94e8be16a8cc
-- title:
--   CSD: ga Mat eq lift
-- statement:
--   The CSD construction uses the ga Mat eq lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L103-L110

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

theorem Formalism.L2.DIV.CSD.gaMat_eq_lift (a : MonoidAlgebra K G) :
    S.gaMat r a = MonoidAlgebra.lift K (Matrix (Fin S.dim) (Fin S.dim) K) G (S.actHom r) a := by sorry
