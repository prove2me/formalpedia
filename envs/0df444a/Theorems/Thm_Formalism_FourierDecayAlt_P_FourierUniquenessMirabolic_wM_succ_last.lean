-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_succ_last
-- name    : Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_succ_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:48.722996+00:00
-- url     : https://prove2.me/theorems/fc71ba1a-00f5-4216-81a8-d2b2ef9b0d1d
-- title:
--   Fourier Uniqueness Mirabolic: w M succ last
-- statement:
--   The Fourier Uniqueness Mirabolic construction uses the w M succ last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L27-L32

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

theorem Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_succ_last {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n) :
    (wMat (n + 1) * Mcoord t X B ρ σ) i.succ (Fin.last n) = B i := by sorry
