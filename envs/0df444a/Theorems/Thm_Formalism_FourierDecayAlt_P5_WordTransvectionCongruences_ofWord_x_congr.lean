-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_x_congr
-- name    : Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_x_congr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:45:39.615422+00:00
-- url     : https://prove2.me/theorems/bc29dc20-a541-4b0a-af39-ab7ca99be09c
-- title:
--   Word Transvection Congruences: of Word x congr
-- statement:
--   The Word Transvection Congruences construction uses the of Word x congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L21-L27

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_x_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).x = (Fr.ofWord L st w).x := by sorry
