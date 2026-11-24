-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_herm_sub_swap
-- name    : Formalism.L2.Th1.H.herm_sub_swap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:04:40.449058+00:00
-- url     : https://prove2.me/theorems/552df033-7b36-460e-b035-29e6e75b391c
-- title:
--   H: herm sub swap
-- statement:
--   The H construction uses the herm sub swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlock.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlock.lean#L13-L17

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_sub_swap

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.herm_sub_swap (H : Sesq V) (hH : IsHerm H) (x y : V) :
    H x y - H y x = 2 * Complex.I * (altE H x y : ℂ) := by sorry
