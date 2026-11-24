-- Prove2me | Theorems.Thm_Formalism_L2_DIV_idemOfSpec_of
-- name    : Formalism.L2.DIV.idemOfSpec_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:29.357399+00:00
-- url     : https://prove2.me/theorems/7332696f-4e9a-41f8-bc0e-a2c508c01b77
-- title:
--   DIV: idem Of Spec of
-- statement:
--   The DIV construction uses the idem Of Spec of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L793-L804
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L793-L804

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.DIV.idemOfSpec_of
    (hidem : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)),
      (∀ χ ∈ X, IsAbsIrrChar χ) → idemOf X * idemOf X = idemOf X) : IdemOfSpec := by sorry
