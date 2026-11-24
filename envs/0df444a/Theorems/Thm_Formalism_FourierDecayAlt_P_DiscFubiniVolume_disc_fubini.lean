-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_disc_fubini
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_fubini
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:47.857849+00:00
-- url     : https://prove2.me/theorems/12e3674f-2047-4cf5-8bd2-1eb27b1a0333
-- title:
--   Disc Fubini Volume: disc fubini
-- statement:
--   The Disc Fubini Volume construction uses the disc fubini property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L49-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean#L49-L115

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

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_fubini {R ρ : ℝ} (hR : 0 < R) :
    ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by sorry
