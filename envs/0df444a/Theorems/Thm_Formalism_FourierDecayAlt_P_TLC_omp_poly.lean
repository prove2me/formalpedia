-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TLC_omp_poly
-- name    : Formalism.FourierDecayAlt.P.TLC.omp_poly
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:41.589894+00:00
-- url     : https://prove2.me/theorems/799b79b1-e44b-47e8-9f2d-fe90c4a168c8
-- title:
--   TLC: omp poly
-- statement:
--   The TLC construction uses the omp poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmpCofLPd.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmpCofLPd.lean#L41-L49

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TLC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.TLC.omp_poly {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (j : Fin k) :
    U.IsPolyDeg (r + 1) (fun g => omC Bs B0 g j) := by sorry
