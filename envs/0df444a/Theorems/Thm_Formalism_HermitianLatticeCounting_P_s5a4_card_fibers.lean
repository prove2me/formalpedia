-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_card_fibers
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_card_fibers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:57.601141+00:00
-- url     : https://prove2.me/theorems/e8ea7984-8aa6-44ed-89b1-4bbcb9ed773e
-- title:
--   P: s5a4 card fibers
-- statement:
--   The P construction uses the s5a4 card fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L646-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L646-L650

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_card_fibers {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) :
    ∑ k, (Nat.card {a // f a = k} : ℤ) = Fintype.card α := by sorry
