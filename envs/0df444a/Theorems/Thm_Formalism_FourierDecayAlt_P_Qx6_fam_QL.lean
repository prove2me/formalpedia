-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_QL
-- name    : Formalism.FourierDecayAlt.P.Qx6.fam_QL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:34:29.140869+00:00
-- url     : https://prove2.me/theorems/b7b5f69b-ba96-4a39-aaac-6b506b53477c
-- title:
--   Qx6: fam QL
-- statement:
--   The Qx6 construction uses the fam QL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1294-L1298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1294-L1298

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.Qx6.fam_QL (hTP : TPreservesFF) (hz : inWb k r z) (hz' : inWb k r z')
    (hd : ∀ c ∈ OmX r, IsDom k r z z' L (Dc c)) (Y : ℂ) (a b : Fin 2) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (h : FamFF k r z z' π π' L Dc Φ) : FamFF k r z z' π π' L Dc (QL k r z z' L Y a b Φ) := by sorry
