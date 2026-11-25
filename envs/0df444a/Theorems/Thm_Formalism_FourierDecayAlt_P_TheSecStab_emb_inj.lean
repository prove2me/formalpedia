-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_emb_inj
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.emb_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:23:05.199425+00:00
-- url     : https://prove2.me/theorems/91c44d7c-f0a6-4187-8998-1614bc243e54
-- title:
--   The Sec Stab: emb inj
-- statement:
--   The The Sec Stab construction uses the emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L311-L316

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

theorem Formalism.FourierDecayAlt.P.TheSecStab.emb_inj {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : embWb k r μ = embWb k r μ') : μ = μ' := by sorry
