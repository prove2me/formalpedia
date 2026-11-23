-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_zero_last
-- name    : Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_zero_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:40.666291+00:00
-- url     : https://prove2.me/theorems/89946b87-b8bf-4122-a862-eacf8f17602e
-- title:
--   Fourier Uniqueness Mirabolic: w M zero last
-- statement:
--   The Fourier Uniqueness Mirabolic construction uses the w M zero last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L48-L53

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_zero_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord t X B ρ σ) 0 (Fin.last n) = σ := by sorry
