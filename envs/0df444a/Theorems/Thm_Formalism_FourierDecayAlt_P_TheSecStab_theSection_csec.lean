-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_theSection_csec
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:24:04.074122+00:00
-- url     : https://prove2.me/theorems/f0ad4dcd-ac7c-564c-8efc-6e3ea4986385
-- title:
--   The Sec Stab: the Section csec
-- statement:
--   The The Sec Stab construction uses the the Section csec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L339-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L339-L345

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq ζ' →
        NF.Stab k r z z' (theSection k r z z') ζ = NF.Stab k r z z' (theSection k r z z') ζ' := by sorry
