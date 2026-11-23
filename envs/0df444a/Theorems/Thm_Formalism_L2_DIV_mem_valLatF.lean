-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_valLatF
-- name    : Formalism.L2.DIV.mem_valLatF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:05.360565+00:00
-- url     : https://prove2.me/theorems/10330201-2815-4159-80b6-51584ed0942f
-- title:
--   DIV: mem val Lat F
-- statement:
--   The DIV construction uses the mem val Lat F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L122-L130

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF

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

theorem Formalism.L2.DIV.mem_valLatF {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {Cl V : Type}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) (x : Fin n → K) :
    x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by sorry
