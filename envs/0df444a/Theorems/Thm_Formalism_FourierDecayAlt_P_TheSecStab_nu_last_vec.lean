-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_nu_last_vec
-- name    : Formalism.FourierDecayAlt.P.TheSecStab.nu_last_vec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:56.770792+00:00
-- url     : https://prove2.me/theorems/07d4c4e6-ab9c-47ba-b60d-0e7be0fc6a63
-- title:
--   The Sec Stab: nu last vec
-- statement:
--   The The Sec Stab construction uses the nu last vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L101-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheSectionStab.lean#L101-L114

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
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.TheSecStab.nu_last_vec (hk : 1 ≤ k) (w s : ℂ) :
    nu k w s *ᵥ Pi.single (Fin.last k) 1 = s • Pi.single 0 1 + w • Pi.single (Fin.last k) 1 := by sorry
