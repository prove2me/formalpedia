-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_mem_invB
-- name    : Formalism.FourierDecayAlt.P.Fr2.mem_invB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:02.339297+00:00
-- url     : https://prove2.me/theorems/4df623e0-8f94-4630-8813-91e3425de05b
-- title:
--   Fr2: mem inv B
-- statement:
--   The Fr2 construction uses the mem inv B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L120-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L120-L136

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr2.mem_invB (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1) :
    Y ∈ (ofWord L st w).inv := by sorry
