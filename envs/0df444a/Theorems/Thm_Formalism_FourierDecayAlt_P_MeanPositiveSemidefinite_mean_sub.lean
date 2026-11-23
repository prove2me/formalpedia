-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_mean_sub
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.mean_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:47.729079+00:00
-- url     : https://prove2.me/theorems/dfbf4732-87f9-4fb1-82fb-3c374de1140d
-- title:
--   Mean Positive Semidefinite: mean sub
-- statement:
--   The Mean Positive Semidefinite construction uses the mean sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L84-L92

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

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.mean_sub {K : Type} (A B : Finset K) (hA : A.card ≠ 0) (hB : B.card ≠ 0) (Y : ℂ)
    (u : K → K → ℂ) :
    Y - ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B, u ρ b =
      ∑ ρ ∈ A, ∑ b ∈ B, ((((A.card : ℝ) * (B.card : ℝ))⁻¹ : ℝ) : ℂ) * (Y - u ρ b) := by sorry
