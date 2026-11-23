-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_posB
-- name    : Formalism.FourierDecayAlt.P.Fr2.qw_posB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:00.044511+00:00
-- url     : https://prove2.me/theorems/c9953ea9-eefe-46b1-a2ce-372ccf7cc40e
-- title:
--   Fr2: qw pos B
-- statement:
--   The Fr2 construction uses the qw pos B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L473-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L473-L489

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

theorem Formalism.FourierDecayAlt.P.Fr2.qw_posB (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1) ∧
      0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re + 1)) : Pos (qw q0 w Y) := by sorry
