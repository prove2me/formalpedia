-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_qw_ne
-- name    : Formalism.FourierDecayAlt.P.Fr2.qw_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:05.485566+00:00
-- url     : https://prove2.me/theorems/2b6ef0fd-4897-428a-af57-0ed48e00e5e8
-- title:
--   Fr2: qw ne
-- statement:
--   The Fr2 construction uses the qw ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleRecOfAdmissibleWord.lean#L28-L42

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

theorem Formalism.FourierDecayAlt.P.Fr2.qw_ne (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ -1) : qw q w Y ≠ 0 := by sorry
