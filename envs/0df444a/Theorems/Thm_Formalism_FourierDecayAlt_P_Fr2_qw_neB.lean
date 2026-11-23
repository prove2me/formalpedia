-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_neB
-- name    : Formalism.FourierDecayAlt.P.Fr2.qw_neB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:04.785349+00:00
-- url     : https://prove2.me/theorems/83a5bf90-59bf-4c19-a03a-b2c557f734d6
-- title:
--   Fr2: qw ne B
-- statement:
--   The Fr2 construction uses the qw ne B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L138-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L138-L154

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

theorem Formalism.FourierDecayAlt.P.Fr2.qw_neB (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1 ∧ Y - ypt l ≠ -1) : qw q w Y ≠ 0 := by sorry
