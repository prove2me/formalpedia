-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_relIndex_ne_zero_of_bound
-- name    : Formalism.L2.Th1.H.relIndex_ne_zero_of_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:12.229115+00:00
-- url     : https://prove2.me/theorems/ba06643b-814e-5669-9357-cead21b9bb72
-- title:
--   H: rel Index ne zero of bound
-- statement:
--   The H construction uses the rel Index ne zero of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L60-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L60-L75

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V]

theorem Formalism.L2.Th1.H.relIndex_ne_zero_of_bound [Module ℂ V] (H K F : AddSubgroup V) [Module.Finite ℤ F] (N M : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hK : ∀ x ∈ K, N • x ∈ F) (hH : ∀ x ∈ F, M • x ∈ H) : H.relIndex K ≠ 0 := by sorry
