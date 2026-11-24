-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_Hpk_fix_of_phi
-- name    : Formalism.FourierDecayAlt.P.FixedPointsGramVector.Hpk_fix_of_phi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:20.653823+00:00
-- url     : https://prove2.me/theorems/0a1b2243-0c47-494a-89c2-bb6dccd9aab6
-- title:
--   Fixed Points Gram Vector: Hpk fix of phi
-- statement:
--   The Fixed Points Gram Vector construction uses the Hpk fix of phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L24-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L24-L85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FixedPointsGramVector.Hpk_fix_of_phi (y : Fin (2 * r + k + 1) → ℂ) (hy : phiL k r y = 0) : Hpk k r *ᵥ y = y := by sorry
