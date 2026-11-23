-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrtM
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrtM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.257801+00:00
-- url     : https://prove2.me/theorems/8abf0859-7ebc-4991-a150-4ebec109c0f5
-- title:
--   Adic: sqrt M
-- statement:
--   The Adic construction uses the sqrt M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L393-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L393-L416

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sqrtM (h : Adic R ϖ) (G N : Matrix (Fin m) (Fin m) K) (hG : ∀ i j, G i j ∈ R)
    (hN : ∀ i j, N i j ∈ R) :
    ∃ Y : Matrix (Fin m) (Fin m) K, (∀ i j, Y i j ∈ R) ∧ Y = N - (ϖ : K) • (Y * G * Y) := by sorry
