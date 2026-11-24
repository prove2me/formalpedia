-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_fiber_card
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_fiber_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:55.377103+00:00
-- url     : https://prove2.me/theorems/0724e736-7f2f-40d5-a4fc-b5c72f2bb91e
-- title:
--   P: s5a4 fiber card
-- statement:
--   The P construction uses the s5a4 fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L601-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L601-L622

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_fiber_card {K : Type} [Field K] [Fintype K] (M : ℕ) (x : Fin (M + 1) → K)
    (hx : x ≠ 0) (c : K) :
    Nat.card {y : Fin (M + 1) → K // ∑ i, x i * y i = c} = Fintype.card K ^ M := by sorry
