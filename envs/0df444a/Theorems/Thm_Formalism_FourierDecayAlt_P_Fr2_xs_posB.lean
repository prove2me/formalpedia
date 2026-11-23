-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_xs_posB
-- name    : Formalism.FourierDecayAlt.P.Fr2.xs_posB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:57.987729+00:00
-- url     : https://prove2.me/theorems/e5cba959-c578-4d23-8c35-21ec2d914ef3
-- title:
--   Fr2: xs pos B
-- statement:
--   The Fr2 construction uses the xs pos B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L460-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L460-L471

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

theorem Formalism.FourierDecayAlt.P.Fr2.xs_posB (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (xs x0 w e Y) := by sorry
