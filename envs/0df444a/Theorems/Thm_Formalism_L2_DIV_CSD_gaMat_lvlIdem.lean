-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_lvlIdem
-- name    : Formalism.L2.DIV.CSD.gaMat_lvlIdem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:32.0856+00:00
-- url     : https://prove2.me/theorems/acbb5a21-62b3-46dc-a2f9-4d0512a5f3fb
-- title:
--   CSD: ga Mat lvl Idem
-- statement:
--   The CSD construction uses the ga Mat lvl Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L229-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L229-L237

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
open Classical

theorem Formalism.L2.DIV.CSD.gaMat_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) :
    S.gaMat r (lvlIdem P ψ) =
      ∑ h : P, ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • S.actMat r (h : G) := by sorry
