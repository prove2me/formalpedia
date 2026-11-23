-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_stdH_apply
-- name    : Formalism.L2.Th1.H.stdH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:46.502175+00:00
-- url     : https://prove2.me/theorems/e13e2043-7cc1-4050-8838-9d41ccc61da8
-- title:
--   H: std H apply
-- statement:
--   The H construction uses the std H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlock.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlock.lean#L172-L178

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
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

theorem Formalism.L2.Th1.H.stdH_apply (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i) := by sorry
