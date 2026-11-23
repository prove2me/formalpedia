-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_mem_sc
-- name    : Formalism.EigenvalueLevelCeiling.mem_sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:21.504489+00:00
-- url     : https://prove2.me/theorems/9e508604-755e-4bf4-8ebc-551eaaffe16d
-- title:
--   Eigenvalue Level Ceiling: mem sc
-- statement:
--   The Eigenvalue Level Ceiling construction uses the mem sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxPsiGood.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxPsiGood.lean#L11-L16

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.mem_sc {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by sorry
