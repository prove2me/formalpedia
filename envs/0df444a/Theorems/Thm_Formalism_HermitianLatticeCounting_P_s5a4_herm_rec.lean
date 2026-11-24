-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_herm_rec
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_herm_rec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:18.791798+00:00
-- url     : https://prove2.me/theorems/3a813b0f-6ce0-49d9-b714-85954ae3d8e8
-- title:
--   P: s5a4 herm rec
-- statement:
--   The P construction uses the s5a4 herm rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L688-L729
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L688-L729

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_herm_rec {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (h2 : finrank K L = 2) (M : ℕ) (c : K) :
    (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) +
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) ^ (2 * M) -
        (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)) := by sorry
