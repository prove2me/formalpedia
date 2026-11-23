-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrt_symm
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:55.861432+00:00
-- url     : https://prove2.me/theorems/ea9f8a98-f41d-4a4e-8177-f493fc54353f
-- title:
--   Adic: sqrt symm
-- statement:
--   The Adic construction uses the sqrt symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L431-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L431-L441

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrt_symm (h : Adic R ϖ) {G N Y : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (e : Y = N - (ϖ : K) • (Y * G * Y))
    (hGs : Gᵀ = G) (hNs : Nᵀ = N) : Yᵀ = Y := by sorry
