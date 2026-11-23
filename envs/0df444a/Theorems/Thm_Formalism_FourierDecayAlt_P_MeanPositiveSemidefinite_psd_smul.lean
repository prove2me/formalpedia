-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_smul
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:51.771458+00:00
-- url     : https://prove2.me/theorems/8eff78ce-84e5-4ef6-a65b-755b2b93d944
-- title:
--   Mean Positive Semidefinite: psd smul
-- statement:
--   The Mean Positive Semidefinite construction uses the psd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L46-L54

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
variable {X : Type}

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_smul {F : Finset X} {k : X → X → ℂ} (c : ℝ) (hc : 0 ≤ c) (hk : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by sorry
