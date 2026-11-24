-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_even_im_hermitian_sub
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.even_im_hermitian_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:16.258164+00:00
-- url     : https://prove2.me/theorems/adfed33d-8049-491c-8451-f4cbcf0c8779
-- title:
--   SC: even im hermitian sub
-- statement:
--   The SC construction uses the even im hermitian sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean#L14-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_even_im_hermitian_sub

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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.even_im_hermitian_sub (a b c e m k : ℤ) (h1 : ¬(2 ∣ a ∧ 2 ∣ b)) (h2 : ¬(2 ∣ c ∧ 2 ∣ e))
    (h3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e)) :
    (2 ∣ m ∧ 2 ∣ k) ∨ (2 ∣ m - a ∧ 2 ∣ k - b) ∨ (2 ∣ m - c ∧ 2 ∣ k - e) ∨ (2 ∣ m - (a + c) ∧ 2 ∣ k - (b + e)) := by sorry
