-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_tuple_count
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_tuple_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:02.25163+00:00
-- url     : https://prove2.me/theorems/caf8e60c-2551-46a6-a4d8-f06a06196676
-- title:
--   P: s5a4 tuple count
-- statement:
--   The P construction uses the s5a4 tuple count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L960-L998
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L960-L998

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false

theorem Formalism.HermitianLatticeCounting.P.s5a4_tuple_count (n : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)).filter
      (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ X * (1 + Real.log X) ^ n := by sorry
