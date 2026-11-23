-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_lvlIdem_mulVec_of_mem
-- name    : Formalism.L2.DIV.CSD.lvlIdem_mulVec_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:32.761233+00:00
-- url     : https://prove2.me/theorems/d9f06518-0215-430c-aeef-8d44bd38d169
-- title:
--   CSD: lvl Idem mul Vec of mem
-- statement:
--   The CSD construction uses the lvl Idem mul Vec of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L269-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L269-L290

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

theorem Formalism.L2.DIV.CSD.lvlIdem_mulVec_of_mem (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin S.dim → K)
    (hx : x ∈ S.lvlPart r P ψ) : (S.gaMat r (lvlIdem P ψ)).mulVec x = x := by sorry
