-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gB_spec
-- name    : Formalism.FourierDecayAlt.P.TheSec.gB_spec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:46:46.186427+00:00
-- url     : https://prove2.me/theorems/b7cd00b5-ef44-4d5c-99f0-9f4f1b15e6dc
-- title:
--   The Sec: g B spec
-- statement:
--   The The Sec construction uses the g B spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSection.lean#L51-L58

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

theorem Formalism.FourierDecayAlt.P.TheSec.gB_spec {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (gB k b T')ᴴ * Hb k * gB k b T' = Hb k ∧
      gB k b T' *ᵥ b = ((Real.sqrt T' : ℝ) : ℂ) • Pi.single (Fin.last k) 1 := by sorry
