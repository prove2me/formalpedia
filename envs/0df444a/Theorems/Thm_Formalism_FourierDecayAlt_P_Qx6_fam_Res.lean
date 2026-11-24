-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_Res
-- name    : Formalism.FourierDecayAlt.P.Qx6.fam_Res
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:48.674808+00:00
-- url     : https://prove2.me/theorems/ac161fb2-8a81-43a6-b290-1024432bc6f0
-- title:
--   Qx6: fam Res
-- statement:
--   The Qx6 construction uses the fam Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1452-L1457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1452-L1457

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.Qx6.fam_Res (hW : WeylLevelElementFacts) (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    {Dc : (Fin r → ℂ) → Set (Mx k r)} (hd : ∀ c ∈ OmX r, IsDom k r z z' l.castSucc (Dc c))
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' l.castSucc Dc Φ) :
    FamFF k r z z' π π' l.succ (stepD l Dc) (Res k r l Φ) := by sorry
