-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_d_m
-- name    : Formalism.FourierDecayAlt.P.Fr8.d_m
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:04:23.813663+00:00
-- url     : https://prove2.me/theorems/05797ebe-b6a5-4397-9bea-a9a85cba6563
-- title:
--   Fr8: d m
-- statement:
--   The Fr8 construction uses the d m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L214-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L214-L242

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr8.d_m (hS : IsStarLevel L) (h : IsFrame L f) (Yb : ℂ) (hr : star Yb = Yb) (h0 : Yb ∈ f.inv)
    (h1 : Yb - 1 ∈ f.inv) :
    f.d L * mf f.hatT (fun Y => io L.GGi * f.xi Y) Yb = star (f.l L (Yb - 1)) * f.d L := by sorry
