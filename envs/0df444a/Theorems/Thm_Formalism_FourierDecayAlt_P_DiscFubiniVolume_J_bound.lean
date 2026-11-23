-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_J_bound
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:52.702795+00:00
-- url     : https://prove2.me/theorems/e9068937-d5f9-4cf9-b0bf-777b49f19253
-- title:
--   Disc Fubini Volume: J bound
-- statement:
--   The Disc Fubini Volume construction uses the J bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L114-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L114-L248

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

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_bound {u : ℝ} (hu : 1 ≤ u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by sorry
