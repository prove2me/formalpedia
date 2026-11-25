-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_hpart2_conj
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.hpart2_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:24.72414+00:00
-- url     : https://prove2.me/theorems/98158adf-8401-4ded-b451-96a59f20a217
-- title:
--   Left Derivative Curves: hpart2 conj
-- statement:
--   The Left Derivative Curves construction uses the hpart2 conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L311-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L311-L315

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
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
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.hpart2_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart2 (Hpk k r) (g⁻¹ * Z * g) = g⁻¹ * hpart2 (Hpk k r) Z * g := by sorry
