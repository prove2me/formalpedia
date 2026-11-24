-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_hasFDerivAt_fsv
-- name    : Formalism.FourierDecayAlt.P5.hasFDerivAt_fsv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:07.810895+00:00
-- url     : https://prove2.me/theorems/bd20c555-2aa3-40ee-bea2-2c792061d590
-- title:
--   P5: has FDeriv At fsv
-- statement:
--   The P5 construction uses the has FDeriv At fsv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L24-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L24-L48

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem Formalism.FourierDecayAlt.P5.hasFDerivAt_fsv {m : ℕ} (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      D (Pi.single l 1) = (t - conj t) * fsv t (c l) ∧
      D (Pi.single l Complex.I) = Complex.I * (t + conj t) * fsv t (c l) := by sorry
