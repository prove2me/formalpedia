-- Prove2me | Theorems.Thm_Formalism_L2_DIV_single_mul_lvlIdem
-- name    : Formalism.L2.DIV.single_mul_lvlIdem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:10.653662+00:00
-- url     : https://prove2.me/theorems/26ee79fc-b4fe-4318-9bac-0561ed0e6ead
-- title:
--   DIV: single mul lvl Idem
-- statement:
--   The DIV construction uses the single mul lvl Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L414-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L414-L416

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.DIV.single_mul_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) (h : P) :
    MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ := by sorry
