-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hasDerivAt_g0
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:21.796818+00:00
-- url     : https://prove2.me/theorems/288654d1-6db9-4a77-8f99-e7bb2c49d98f
-- title:
--   Disc Fubini Volume: has Deriv At g0
-- statement:
--   The Disc Fubini Volume construction uses the has Deriv At g0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L82-L88

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g0 {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g0 (g1 t) t := by sorry
