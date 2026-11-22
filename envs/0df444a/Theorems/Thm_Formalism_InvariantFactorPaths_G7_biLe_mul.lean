-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_mul
-- name    : Formalism.InvariantFactorPaths.G7.biLe_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:56.320247+00:00
-- url     : https://prove2.me/theorems/db8a6bd1-5e98-4a21-8f4e-e9ecd402d409
-- title:
--   G7: bi Le mul
-- statement:
--   The G7 construction uses the bi Le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L139-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L139-L159

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.biLe_mul {n0 n0' : ι →₀ ℕ} {W W' : MvPolynomial κ (MvPolynomial ι K)} (h : BiLe n0 W)
    (h' : BiLe n0' W') : BiLe (n0 + n0') (W * W') := by sorry
