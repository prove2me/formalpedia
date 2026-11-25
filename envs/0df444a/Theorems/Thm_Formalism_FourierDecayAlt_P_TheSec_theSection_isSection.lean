-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_theSection_isSection
-- name    : Formalism.FourierDecayAlt.P.TheSec.theSection_isSection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:50.294868+00:00
-- url     : https://prove2.me/theorems/6110aebc-6004-4159-a980-90529663118f
-- title:
--   The Sec: the Section is Section
-- statement:
--   The The Sec construction uses the the Section is Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L340-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L340-L358

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)

theorem Formalism.FourierDecayAlt.P.TheSec.theSection_isSection (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') := by sorry
