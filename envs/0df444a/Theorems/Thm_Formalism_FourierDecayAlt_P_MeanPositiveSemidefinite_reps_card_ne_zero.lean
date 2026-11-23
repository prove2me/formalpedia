-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_reps_card_ne_zero
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.reps_card_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:57.110809+00:00
-- url     : https://prove2.me/theorems/dd975cc8-038f-4588-8961-1c80cfee402b
-- title:
--   Mean Positive Semidefinite: reps card ne zero
-- statement:
--   The Mean Positive Semidefinite construction uses the reps card ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L94-L97

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

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.reps_card_ne_zero {K : Type} [CommRing K] {S : Finset K} {L M : AddSubgroup K}
    (h : IsReps S L M) : S.card ≠ 0 := by sorry
