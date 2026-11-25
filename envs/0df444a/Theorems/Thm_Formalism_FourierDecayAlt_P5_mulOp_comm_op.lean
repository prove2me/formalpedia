-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_mulOp_comm_op
-- name    : Formalism.FourierDecayAlt.P5.mulOp_comm_op
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:28.995484+00:00
-- url     : https://prove2.me/theorems/59f99e85-7536-46e0-89e1-b4f3b8b602bc
-- title:
--   P5: mul Op comm op
-- statement:
--   The P5 construction uses the mul Op comm op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L204-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L204-L213

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
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

theorem Formalism.FourierDecayAlt.P5.mulOp_comm_op (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π')) (t : ℂ) (l : Fin r)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    {l' : Fin r} (hl : l' ≠ l) (i : Fin 6) : W * X.op l' i = X.op l' i * W := by sorry
