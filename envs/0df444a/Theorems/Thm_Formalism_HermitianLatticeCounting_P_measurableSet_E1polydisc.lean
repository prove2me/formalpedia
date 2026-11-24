-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_measurableSet_E1polydisc
-- name    : Formalism.HermitianLatticeCounting.P.measurableSet_E1polydisc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:52.383+00:00
-- url     : https://prove2.me/theorems/dd4cf3da-9d3b-44a1-95df-69ac8e028a69
-- title:
--   P: measurable Set E1polydisc
-- statement:
--   The P construction uses the measurable Set E1polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L192-L194

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.measurableSet_E1polydisc {ι : Type} [Fintype ι] (ro : ℝ) (D : ι → ℂ) : MeasurableSet (CenteredPolydisc ro D) := by sorry
