-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_mul_right
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.MemM.mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:55.312801+00:00
-- url     : https://prove2.me/theorems/1ce06b40-5299-4b7b-8249-121579850c15
-- title:
--   Mem M: mul right
-- statement:
--   The Mem M construction uses the mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L377-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L377-L380

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.MemM.mul_right {Λ : Submodule R K} {A X : Matrix (Fin m) (Fin m) K} (hA : ∀ i j, A i j ∈ R)
    (hX : MemM Λ X) : MemM Λ (X * A) := by sorry
