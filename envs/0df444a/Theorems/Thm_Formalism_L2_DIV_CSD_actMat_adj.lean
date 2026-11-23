-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_actMat_adj
-- name    : Formalism.L2.DIV.CSD.actMat_adj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:54.889934+00:00
-- url     : https://prove2.me/theorems/b82a8e99-fdaf-48db-a2e0-b47dc91d0530
-- title:
--   CSD: act Mat adj
-- statement:
--   The CSD construction uses the act Mat adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L202-L207

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

theorem Formalism.L2.DIV.CSD.actMat_adj (hr : S.ActGood r) (t : G) :
    (S.actMat r t)ᴴ * S.H = S.H * S.actMat r t⁻¹ := by sorry
