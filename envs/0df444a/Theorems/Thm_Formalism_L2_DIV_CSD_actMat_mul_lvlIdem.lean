-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_actMat_mul_lvlIdem
-- name    : Formalism.L2.DIV.CSD.actMat_mul_lvlIdem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:29.385804+00:00
-- url     : https://prove2.me/theorems/b6b1329c-8214-4784-8ef8-6955299de1a3
-- title:
--   CSD: act Mat mul lvl Idem
-- statement:
--   The CSD construction uses the act Mat mul lvl Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L261-L267

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

theorem Formalism.L2.DIV.CSD.actMat_mul_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) (k : P) :
    S.actMat r (k : G) * S.gaMat r (lvlIdem P ψ) = ((ψ k : Kˣ) : K) • S.gaMat r (lvlIdem P ψ) := by sorry
