-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrt_lip
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_lip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:58.543995+00:00
-- url     : https://prove2.me/theorems/5e910937-002f-42e6-8106-7ecfdf8ccdb6
-- title:
--   Adic: sqrt lip
-- statement:
--   The Adic construction uses the sqrt lip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L418-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L418-L429

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_lip (h : Adic R ϖ) {G N N' Y Y' : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R)
    (e : Y = N - (ϖ : K) • (Y * G * Y)) (e' : Y' = N' - (ϖ : K) • (Y' * G * Y'))
    (Λ : Submodule R K) (hN : MemM Λ (N - N')) : MemM Λ (Y - Y') := by sorry
