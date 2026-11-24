-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_dmin_star_pd
-- name    : Formalism.FourierDecayAlt.P.dmin_star_pd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:34:25.606455+00:00
-- url     : https://prove2.me/theorems/90579db4-e6a7-48eb-8187-fc2e428ebff0
-- title:
--   P: dmin star pd
-- statement:
--   The P construction uses the dmin star pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L181-L183

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PartialDerivativeAlgebra

theorem Formalism.FourierDecayAlt.P.dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by sorry
