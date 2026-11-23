-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_psd_sum
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:00.669781+00:00
-- url     : https://prove2.me/theorems/a74ae322-5ca2-40f8-891d-dd04b1688590
-- title:
--   Mean Positive Semidefinite: psd sum
-- statement:
--   The Mean Positive Semidefinite construction uses the psd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L35-L44

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

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_sum {ι : Type} (S : Finset ι) {F : Finset X} {k : ι → X → X → ℂ}
    (hk : ∀ i ∈ S, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ S, k i x y) := by sorry
