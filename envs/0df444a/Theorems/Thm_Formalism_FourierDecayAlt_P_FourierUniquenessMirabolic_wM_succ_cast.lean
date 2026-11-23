-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_succ_cast
-- name    : Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_succ_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:38.601609+00:00
-- url     : https://prove2.me/theorems/8028223a-1be5-4a28-805d-232539269e40
-- title:
--   Fourier Uniqueness Mirabolic: w M succ cast
-- statement:
--   The Fourier Uniqueness Mirabolic construction uses the w M succ cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L34-L39

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

theorem Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_succ_cast {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i j : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ j.castSucc = t * (1 : Matrix (Fin n) (Fin n) ℂ) i j + X i j := by sorry
