-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_ckOn_smul
-- name    : Formalism.FourierDecayAlt.P.Qb1.ckOn_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:11.223743+00:00
-- url     : https://prove2.me/theorems/7ae1b1fc-1651-401f-b6a6-a90e8d293503
-- title:
--   Qb1: ck On smul
-- statement:
--   The Qb1 construction uses the ck On smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CasimirEigenvalueCoefficients.lean#L42-L50

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

theorem Formalism.FourierDecayAlt.P.Qb1.ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mx k r → E} (s : ℂ)
    (h : CkOn m (GV k r) f) : CkOn m (GV k r) (fun g => s • f g) := by sorry
