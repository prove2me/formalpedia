-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_ms_rkK_bot
-- name    : Formalism.BranchingDeterminantCap.ms_rkK_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:50.741311+00:00
-- url     : https://prove2.me/theorems/1b592667-176f-4da6-830d-99a8bc41a030
-- title:
--   Branching Determinant Cap: ms rk K bot
-- statement:
--   The Branching Determinant Cap construction uses the ms rk K bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/MapScale.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/MapScale.lean#L19-L21

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
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
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.BranchingDeterminantCap.ms_rkK_bot : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by sorry
