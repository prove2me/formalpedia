-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_xi_congr
-- name    : Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_xi_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:06.570494+00:00
-- url     : https://prove2.me/theorems/c66d04f1-a8f6-49a8-b108-ee641c9eaea5
-- title:
--   Word Transvection Congruences: of Word xi congr
-- statement:
--   The Word Transvection Congruences construction uses the of Word xi congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L37-L43

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

theorem Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_xi_congr (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by sorry
