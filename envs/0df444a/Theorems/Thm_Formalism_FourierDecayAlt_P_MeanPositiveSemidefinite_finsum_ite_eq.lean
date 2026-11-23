-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanPositiveSemidefinite_finsum_ite_eq
-- name    : Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finsum_ite_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:56.239941+00:00
-- url     : https://prove2.me/theorems/c34fb713-c733-461e-b659-1cc56ade7513
-- title:
--   Mean Positive Semidefinite: finsum ite eq
-- statement:
--   The Mean Positive Semidefinite construction uses the finsum ite eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean#L75-L82

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

theorem Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finsum_ite_eq {α : Type} (S : Finset α) (p : α → Prop) [DecidablePred p] (f : α → ℂ)
    (hS : ∀ x, p x → x ∈ S) :
    ∑ᶠ x, (if p x then f x else 0) = ∑ x ∈ S, if p x then f x else 0 := by sorry
