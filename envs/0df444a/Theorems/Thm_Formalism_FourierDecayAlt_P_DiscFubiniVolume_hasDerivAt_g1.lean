-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hasDerivAt_g1
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:15.755036+00:00
-- url     : https://prove2.me/theorems/6e936a98-5b9b-42ef-92a1-0e1aadb5b48e
-- title:
--   Disc Fubini Volume: has Deriv At g1
-- statement:
--   The Disc Fubini Volume construction uses the has Deriv At g1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L90-L102

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

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_g1 {t : ℝ} (ht : t ^ 2 < 1) : HasDerivAt g1 (g2 t) t := by sorry
