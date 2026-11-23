-- Prove2me | Theorems.Thm_Formalism_L2_DIV_subHasRat_of_span
-- name    : Formalism.L2.DIV.subHasRat_of_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:17.947813+00:00
-- url     : https://prove2.me/theorems/1d517d3e-8ce7-4e68-b2b9-5e8627ac823d
-- title:
--   DIV: sub Has Rat of span
-- statement:
--   The DIV construction uses the sub Has Rat of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L44-L52

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
variable {K : Type} [Field K] [StarRing K] {n : ℕ}

theorem Formalism.L2.DIV.subHasRat_of_span (Z : Submodule K (Fin n → K)) (T : Set (Fin n → K))
    (hT : Submodule.span K T = Z) (hrat : ∀ v ∈ T, ∀ i, v i ∈ cmMax K) : SubHasRatBasis Z := by sorry
