-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gA_spec
-- name    : Formalism.FourierDecayAlt.P.TheSec.gA_spec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:51.538167+00:00
-- url     : https://prove2.me/theorems/8630af78-8c6a-4b20-8a38-c0ddfc3431b0
-- title:
--   The Sec: g A spec
-- statement:
--   The The Sec construction uses the g A spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L42-L49

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

theorem Formalism.FourierDecayAlt.P.TheSec.gA_spec {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    (gA k a T)ᴴ * Hb k * gA k a T = Hb k ∧
      gA k a T *ᵥ (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = a := by sorry
