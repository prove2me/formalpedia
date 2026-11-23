-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ibp2
-- name    : Formalism.FourierDecayAlt.P.DiscFubiniVolume.ibp2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:15.03653+00:00
-- url     : https://prove2.me/theorems/459d6163-c553-45f2-874e-ead13e27dece
-- title:
--   Disc Fubini Volume: ibp2
-- statement:
--   The Disc Fubini Volume construction uses the ibp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L28-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean#L28-L73

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

theorem Formalism.FourierDecayAlt.P.DiscFubiniVolume.ibp2 {φ φ' φ'' : ℝ → ℝ} {α β u : ℝ} (hαβ : α ≤ β) (hu : 0 < u)
    (h1 : ∀ x ∈ uIcc α β, HasDerivAt φ (φ' x) x) (h2 : ∀ x ∈ uIcc α β, HasDerivAt φ' (φ'' x) x)
    (h3 : ContinuousOn φ'' (uIcc α β)) :
    ‖∫ t in α..β, (φ t : ℂ) * ee u t‖ ≤
      (|φ α| + |φ β|) / u + ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 := by sorry
