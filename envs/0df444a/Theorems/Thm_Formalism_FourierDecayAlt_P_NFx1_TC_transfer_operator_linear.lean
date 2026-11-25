-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_transfer_operator_linear
-- name    : Formalism.FourierDecayAlt.P.NFx1.TC.transfer_operator_linear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:05.245281+00:00
-- url     : https://prove2.me/theorems/c4b8ed98-beb0-55d9-a8ba-93a6fe21cdb5
-- title:
--   TC: transfer operator linear
-- statement:
--   The TC construction uses the transfer operator linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L730-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L730-L743

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.NFx1.TC.transfer_operator_linear {f₁ f₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₁)
    (h₂ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₂) (Y : ℂ) (a b : Fin 2) (s₁ s₂ : ℂ) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    tL k r z z' (Fin.last r) Y a b (fun y => s₁ • f₁ y + s₂ • f₂ y) g =
      s₁ • tL k r z z' (Fin.last r) Y a b f₁ g + s₂ • tL k r z z' (Fin.last r) Y a b f₂ g := by sorry
