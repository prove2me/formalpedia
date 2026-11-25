-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_uwset_block
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.uwset_block
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:23:50.407326+00:00
-- url     : https://prove2.me/theorems/7ad2fc9a-3213-4f5c-8863-41f16123f352
-- title:
--   The Sec Stab: uwset block
-- statement:
--   The The Sec Stab construction uses the uwset block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L302-L309

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

theorem Formalism.FourierDecayAlt.P.TheSecStab.uwset_block {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {g : Mat k r} (hg : g ∈ UWset k r z) :
    ∃ μ ∈ UH (Hb k), g = embWb k r μ ∧ μ *ᵥ wbPart k r z = wbPart k r z := by sorry
