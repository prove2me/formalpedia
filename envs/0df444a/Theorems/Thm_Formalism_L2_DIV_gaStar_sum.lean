-- Prove2me | Theorems.Thm_Formalism_L2_DIV_gaStar_sum
-- name    : Formalism.L2.DIV.gaStar_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.492216+00:00
-- url     : https://prove2.me/theorems/c6307f19-aac3-40ad-bb54-41453c8adedd
-- title:
--   DIV: ga Star sum
-- statement:
--   The DIV construction uses the ga Star sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L378-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L378-L383

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

theorem Formalism.L2.DIV.gaStar_sum [StarRing K] {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) :
    gaStar (∑ i ∈ s, f i) = ∑ i ∈ s, gaStar (f i) := by sorry
