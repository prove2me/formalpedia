-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_evR_smul
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.evR_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:41.371652+00:00
-- url     : https://prove2.me/theorems/36954a44-37a5-45ac-8013-16e3259f203b
-- title:
--   Word Monic Extraction: ev R smul
-- statement:
--   The Word Monic Extraction construction uses the ev R smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L80-L85

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.evR_smul (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by sorry
