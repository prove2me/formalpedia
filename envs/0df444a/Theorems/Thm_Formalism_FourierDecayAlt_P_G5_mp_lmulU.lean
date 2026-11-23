-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_lmulU
-- name    : Formalism.FourierDecayAlt.P.G5.mp_lmulU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:09.980709+00:00
-- url     : https://prove2.me/theorems/c56255ed-4bbb-44f3-8c12-859fd3b0a16f
-- title:
--   G5: mp lmul U
-- statement:
--   The G5 construction uses the mp lmul U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L344-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L344-L370

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.mp_lmulU (β : ℂ) : ∀ (n : ℕ) (k : UT n → ℂ),
    MeasurePreserving (fun u : UT n → ℂ => coordU (upper k * upper u)) (muPi β (UT n)) (muPi β (UT n)) := by sorry
