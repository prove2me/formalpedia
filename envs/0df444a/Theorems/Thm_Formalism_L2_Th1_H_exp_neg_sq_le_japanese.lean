-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_exp_neg_sq_le_japanese
-- name    : Formalism.L2.Th1.H.exp_neg_sq_le_japanese
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:48.985173+00:00
-- url     : https://prove2.me/theorems/7addc069-2dbd-4d19-a63d-3d243c2d5101
-- title:
--   H: exp neg sq le japanese
-- statement:
--   The H construction uses the exp neg sq le japanese property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L82-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L82-L107

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

theorem Formalism.L2.Th1.H.exp_neg_sq_le_japanese {a : ℝ} (ha : 0 < a) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a * t ^ 2) ≤ Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * (1 + t) ^ (-((2 * m : ℕ) : ℝ)) := by sorry
