-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_finite_classes
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finite_classes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:13.380377+00:00
-- url     : https://prove2.me/theorems/a6ec0e6c-69ca-4586-8268-bacef824e612
-- title:
--   Mean Positive Semidefinite: finite classes
-- statement:
--   The Mean Positive Semidefinite construction uses the finite classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L58-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L58-L73

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

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finite_classes {K : Type} [AddCommGroup K] (R P : AddSubgroup K) (h : R.relIndex P ≠ 0) :
    {x : K ⧸ R | (Quotient.out x : K) ∈ P}.Finite := by sorry
