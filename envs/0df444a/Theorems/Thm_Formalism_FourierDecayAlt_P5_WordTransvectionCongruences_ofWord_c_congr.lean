-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_c_congr
-- name    : Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:20.230904+00:00
-- url     : https://prove2.me/theorems/e5e17002-a8e9-55f8-8ef8-6a4357d2b7f5
-- title:
--   Word Transvection Congruences: of Word c congr
-- statement:
--   The Word Transvection Congruences construction uses the of Word c congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L53-L67

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

theorem Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by sorry
