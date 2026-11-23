-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourierUniquenessMirabolic_wM_redOf
-- name    : Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_redOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:11.922637+00:00
-- url     : https://prove2.me/theorems/11d0365c-f250-4f14-af9f-b4b2ea1bdca2
-- title:
--   Fourier Uniqueness Mirabolic: w M red Of
-- statement:
--   The Fourier Uniqueness Mirabolic construction uses the w M red Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L69-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourierUniquenessMirabolic.lean#L69-L115

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

theorem Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.wM_redOf (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by sorry
