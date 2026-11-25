-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TLC_omp_adj_pd
-- name    : Formalism.FourierDecayAlt.P.TLC.omp_adj_pd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:26:48.420276+00:00
-- url     : https://prove2.me/theorems/2b03f8bf-703e-4012-96ac-eb9de427b901
-- title:
--   TLC: omp adj pd
-- statement:
--   The TLC construction uses the omp adj pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmpCofLPd.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmpCofLPd.lean#L15-L26

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

theorem Formalism.FourierDecayAlt.P.TLC.omp_adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by sorry
