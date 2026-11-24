-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_dual_vector_eq_zeta
-- name    : Formalism.FourierDecayAlt.P.Qx2.sum_dual_vector_eq_zeta
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:39.980202+00:00
-- url     : https://prove2.me/theorems/c8f43b79-9f2e-4124-91ad-9eab28c01f3f
-- title:
--   Qx2: sum dual vector eq zeta
-- statement:
--   The Qx2 construction uses the sum dual vector eq zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L823-L829
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L823-L829

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.Qx2.sum_dual_vector_eq_zeta (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (g : Mx k r) :
    ∑ j, ybv k r z i g j * xv k r z' i j = zetaL k r z z' i g := by sorry
