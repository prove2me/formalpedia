-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_expand
-- name    : Formalism.FourierDecayAlt.P.Qx2.herm_expand
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:21:01.481549+00:00
-- url     : https://prove2.me/theorems/8a54d9af-15d0-4e8a-b7ea-39f79f7db22e
-- title:
--   Qx2: herm expand
-- statement:
--   The Qx2 construction uses the herm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L791-L794
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L791-L794

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

theorem Formalism.FourierDecayAlt.P.Qx2.herm_expand (M : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ v) w = ∑ p, herm (Hpk k r) (M *ᵥ bvec p) w * v p := by sorry
