-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_contDiff_fsv_coord
-- name    : Formalism.FourierDecayAlt.P5.contDiff_fsv_coord
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:39:39.587927+00:00
-- url     : https://prove2.me/theorems/2283375e-a025-488d-a2f2-7f6cfd77aa08
-- title:
--   P5: cont Diff fsv coord
-- statement:
--   The P5 construction uses the cont Diff fsv coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermMulVecMulVec.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermMulVecMulVec.lean#L61-L63

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P5.contDiff_fsv_coord (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) := by sorry
