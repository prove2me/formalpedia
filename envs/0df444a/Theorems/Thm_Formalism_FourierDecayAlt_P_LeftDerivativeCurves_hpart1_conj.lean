-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_hpart1_conj
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.hpart1_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:57.968911+00:00
-- url     : https://prove2.me/theorems/7d4d6458-efce-45b0-9cca-ab7ea0b0033f
-- title:
--   Left Derivative Curves: hpart1 conj
-- statement:
--   The Left Derivative Curves construction uses the hpart1 conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L305-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L305-L309

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

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.hpart1_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    hpart1 (Hpk k r) (g⁻¹ * Z * g) = g⁻¹ * hpart1 (Hpk k r) Z * g := by sorry
