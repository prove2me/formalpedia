-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_norm_fiber
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_norm_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:58.756073+00:00
-- url     : https://prove2.me/theorems/f22b9df1-7f6c-4c4c-9027-9a45be5c7b14
-- title:
--   P: s5a4 norm fiber
-- statement:
--   The P construction uses the s5a4 norm fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L652-L686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L652-L686

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_norm_fiber {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (h2 : finrank K L = 2) (d : K) (hd : d ≠ 0) :
    (Nat.card {y : L // Algebra.norm K y = d} : ℤ) = Fintype.card K + 1 := by sorry
