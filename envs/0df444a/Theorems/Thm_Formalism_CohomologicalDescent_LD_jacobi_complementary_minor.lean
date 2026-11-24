-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_jacobi_complementary_minor
-- name    : Formalism.CohomologicalDescent.LD.jacobi_complementary_minor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:01.012664+00:00
-- url     : https://prove2.me/theorems/55a6bc52-50c2-4fc6-b423-14efe0aab69d
-- title:
--   LD: jacobi complementary minor
-- statement:
--   The LD construction uses the jacobi complementary minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L279-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L279-L303

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.jacobi_complementary_minor {R : Type*} [CommRing R] {m n₁ n₂ : Type*} [Fintype m] [DecidableEq m]
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (A : Matrix m m R) (ρ γ : n₁ ⊕ n₂ ≃ m) :
    (A.submatrix ρ γ).det * (Matrix.of fun i j : n₁ => A.adjugate (γ (Sum.inl j)) (ρ (Sum.inl i))).det =
      A.det ^ Fintype.card n₁ * (Matrix.of fun i j : n₂ => A (ρ (Sum.inr i)) (γ (Sum.inr j))).det := by sorry
