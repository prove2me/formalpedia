-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_jdCCLowerQ
-- name    : Formalism.FourierDecayAlt.P.CutBP.jdCCLowerQ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:23.462184+00:00
-- url     : https://prove2.me/theorems/2aedf7a2-4abf-455a-b48c-d1cf0dacd5c9
-- title:
--   Cut BP: jd CCLower Q
-- statement:
--   The Cut BP construction uses the jd CCLower Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutNFApxDomThQ.lean#L41-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutNFApxDomThQ.lean#L41-L98

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutBP.jdCCLowerQ {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ)
    (hd : 0 ≤ d) (hG : CutMP.GlobCoef Θ d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CkOn ⊤ (B.GV k r) F →
      B.CCle A (m + B.opOrder Θ) F b → B.CCle (A - d) m (B.opApply Θ F) (K * b) := by sorry
