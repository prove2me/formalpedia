-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_disc_scale
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_scale
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:13:18.620057+00:00
-- url     : https://prove2.me/theorems/f80e984f-c398-46d1-981b-640a28583633
-- title:
--   Disc Fubini Volume: disc scale
-- statement:
--   The Disc Fubini Volume construction uses the disc scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L117-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L117-L145

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_scale {R ρ : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t =
      ((2 * R ^ 2 : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s := by sorry
