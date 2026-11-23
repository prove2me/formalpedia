-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_pos
-- name    : Formalism.FourierDecayAlt.P.Fr2.qw_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:15.621708+00:00
-- url     : https://prove2.me/theorems/89dc9388-b10f-4dc8-be4b-a5aa6d198ff0
-- title:
--   Fr2: qw pos
-- statement:
--   The Fr2 construction uses the qw pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L396-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L396-L411

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

theorem Formalism.FourierDecayAlt.P.Fr2.qw_pos (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (qw q0 w Y) := by sorry
