-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_stab_sub
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.stab_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:24:35.716385+00:00
-- url     : https://prove2.me/theorems/12a8febb-ab9d-571b-aee3-a19bdff1905c
-- title:
--   The Sec Stab: stab sub
-- statement:
--   The The Sec Stab construction uses the stab sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L318-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L318-L337

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

theorem Formalism.FourierDecayAlt.P.TheSecStab.stab_sub (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ ζ' : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    (hζ' : Tz k r z * Tz k r z' < Complex.normSq ζ') (p : Mat k r × Mat k r)
    (hp : p ∈ NF.Stab k r z z' (theSection k r z z') ζ) : p ∈ NF.Stab k r z z' (theSection k r z z') ζ' := by sorry
