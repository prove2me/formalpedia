-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_radSp_regular
-- name    : Formalism.FourierDecayAlt.P5.radSp_regular
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:42:40.045267+00:00
-- url     : https://prove2.me/theorems/ee6c59c1-d575-482f-b633-6604ac2df26b
-- title:
--   P5: rad Sp regular
-- statement:
--   The P5 construction uses the rad Sp regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L98-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L98-L125

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
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P5.radSp_regular (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by sorry
