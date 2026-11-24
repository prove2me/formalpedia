-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_periodLatticeFactsSplitOfGeneral
-- name    : Formalism.FourierDecayAlt.P.periodLatticeFactsSplitOfGeneral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:07.165805+00:00
-- url     : https://prove2.me/theorems/490fa28a-80f8-4d40-bf5b-17652f59c78f
-- title:
--   P: period Lattice Facts Split Of General
-- statement:
--   The P construction uses the period Lattice Facts Split Of General property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PeriodLatticeFactsSplitOfGeneral.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PeriodLatticeFactsSplitOfGeneral.lean#L186-L188

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.periodLatticeFactsSplitOfGeneral : Formalism.FourierDecayAlt.S6.TextFromGeneral := by sorry
