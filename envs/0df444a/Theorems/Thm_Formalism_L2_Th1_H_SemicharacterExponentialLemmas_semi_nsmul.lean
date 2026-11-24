-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_semi_nsmul
-- name    : Formalism.L2.Th1.H.SemicharacterExponentialLemmas.semi_nsmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:52.190414+00:00
-- url     : https://prove2.me/theorems/a1c4f2d5-d78f-400c-af89-c443a1da565b
-- title:
--   Semicharacter Exponential Lemmas: semi nsmul
-- statement:
--   The Semicharacter Exponential Lemmas construction uses the semi nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L47-L67

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
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
open Formalism.L2.Th1.H.SemicharacterExponentialLemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.SemicharacterExponentialLemmas.semi_nsmul {H : Sesq V} (hH : IsHerm H) {Λ : AddSubgroup V} {α : V → ℂ}
    (hα : IsSemiChar H Λ α) {x : V} (hx : x ∈ Λ) (k : ℕ) : α (k • x) = α x ^ (k ^ 2) := by sorry
