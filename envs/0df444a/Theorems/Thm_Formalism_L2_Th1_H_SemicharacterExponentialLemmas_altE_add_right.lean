-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_add_right
-- name    : Formalism.L2.Th1.H.SemicharacterExponentialLemmas.altE_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:12.713347+00:00
-- url     : https://prove2.me/theorems/c17b20e3-4990-4367-81f8-2288f856ba0c
-- title:
--   Semicharacter Exponential Lemmas: alt E add right
-- statement:
--   The Semicharacter Exponential Lemmas construction uses the alt E add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L17-L18

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

theorem Formalism.L2.Th1.H.SemicharacterExponentialLemmas.altE_add_right (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by sorry
