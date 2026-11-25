-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_tl_smul
-- name    : Formalism.FourierDecayAlt.P.NFx1.TC.tl_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:21:53.633798+00:00
-- url     : https://prove2.me/theorems/9d40a1fc-deed-45ae-bac5-f800941543fb
-- title:
--   TC: tl smul
-- statement:
--   The TC construction uses the tl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L745-L750
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean#L745-L750

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

theorem Formalism.FourierDecayAlt.P.NFx1.TC.tl_smul {f : Mx k r → (Wq →L[ℂ] Wp)} (h : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f)
    (Y : ℂ) (a b : Fin 2) (s : ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    tL k r z z' (Fin.last r) Y a b (fun y => s • f y) g = s • tL k r z z' (Fin.last r) Y a b f g := by sorry
