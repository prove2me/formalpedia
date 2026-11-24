-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_ckOn_congr
-- name    : Formalism.FourierDecayAlt.P.Qb1.ckOn_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:15.290802+00:00
-- url     : https://prove2.me/theorems/42169093-9b53-472e-847b-3c6c145ecb77
-- title:
--   Qb1: ck On congr
-- statement:
--   The Qb1 construction uses the ck On congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L25-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

theorem Formalism.FourierDecayAlt.P.Qb1.ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by sorry
