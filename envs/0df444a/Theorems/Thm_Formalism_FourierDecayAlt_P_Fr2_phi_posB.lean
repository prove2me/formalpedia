-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_phi_posB
-- name    : Formalism.FourierDecayAlt.P.Fr2.phi_posB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:40.773799+00:00
-- url     : https://prove2.me/theorems/36293593-77a8-4663-99b2-823e025da5e9
-- title:
--   Fr2: phi pos B
-- statement:
--   The Fr2 construction uses the phi pos B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L450-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L450-L458

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

theorem Formalism.FourierDecayAlt.P.Fr2.phi_posB (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0)
    (h : 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (phiL l Y) := by sorry
