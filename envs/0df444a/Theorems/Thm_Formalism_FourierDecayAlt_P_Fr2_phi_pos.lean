-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_phi_pos
-- name    : Formalism.FourierDecayAlt.P.Fr2.phi_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:37.730142+00:00
-- url     : https://prove2.me/theorems/5c39567f-4a7b-456c-980a-1737574c172e
-- title:
--   Fr2: phi pos
-- statement:
--   The Fr2 construction uses the phi pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L373-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L373-L381

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr2.phi_pos (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0) (h : 1 < |Y.re - l.pt.re|) :
    Pos (phiL l Y) := by sorry
