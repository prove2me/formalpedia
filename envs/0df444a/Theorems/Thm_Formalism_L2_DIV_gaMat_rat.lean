-- Prove2me | Theorems.Thm_Formalism_L2_DIV_gaMat_rat
-- name    : Formalism.L2.DIV.gaMat_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:23.305846+00:00
-- url     : https://prove2.me/theorems/47372f33-b35d-416f-a8b7-b4ef28a7f5e2
-- title:
--   DIV: ga Mat rat
-- statement:
--   The DIV construction uses the ga Mat rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1059-L1066
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1059-L1066

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

theorem Formalism.L2.DIV.gaMat_rat {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (hr : S.ActRat r) (a : MonoidAlgebra K G)
    (ha : ∀ t, a.coeff t ∈ cmMax K) (i j : Fin S.dim) : S.gaMat r a i j ∈ cmMax K := by sorry
