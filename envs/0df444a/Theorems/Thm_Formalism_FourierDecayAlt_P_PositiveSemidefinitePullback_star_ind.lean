-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_star_ind
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.star_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:44.591016+00:00
-- url     : https://prove2.me/theorems/1da2b942-b53b-4526-a330-159da0ca829c
-- title:
--   Positive Semidefinite Pullback: star ind
-- statement:
--   The Positive Semidefinite Pullback construction uses the star ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L29-L32

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.star_ind {α : Type} (Y A : Finset α) : star (ind Y A) = ind Y A := by sorry
