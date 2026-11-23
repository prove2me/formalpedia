-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_exp_neg_le_factorial_div
-- name    : Formalism.L2.Th1.H.exp_neg_le_factorial_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:27.840304+00:00
-- url     : https://prove2.me/theorems/e4afb0a8-a24f-4e38-8a1f-663b10e34949
-- title:
--   H: exp neg le factorial div
-- statement:
--   The H construction uses the exp neg le factorial div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L9-L15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.exp_neg_le_factorial_div {s : ℝ} (hs : 0 < s) (n : ℕ) : Real.exp (-s) ≤ (n ! : ℝ) / s ^ n := by sorry
