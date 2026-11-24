-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fderiv_dir
-- name    : Formalism.FourierDecayAlt.P.Qx6.fderiv_dir
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:35:05.660322+00:00
-- url     : https://prove2.me/theorems/a3c98450-cf7c-427e-959d-918d68232f28
-- title:
--   Qx6: fderiv dir
-- statement:
--   The Qx6 construction uses the fderiv dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1020-L1036
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1020-L1036

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Qx6.fderiv_dir (a : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (κ : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c)
    (hev : ∀ᶠ s in 𝓝 (c a), f₁ (Function.update c a s) = κ • f₂ (Function.update c a s)) (v : ℂ) :
    fderiv ℝ f₁ c (Pi.single a v) = κ • fderiv ℝ f₂ c (Pi.single a v) := by sorry
