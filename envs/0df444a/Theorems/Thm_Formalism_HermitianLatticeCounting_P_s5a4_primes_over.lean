-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_primes_over
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_primes_over
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:23.612867+00:00
-- url     : https://prove2.me/theorems/07247bcc-3e1f-4c79-a5e1-439b9e6ed811
-- title:
--   P: s5a4 primes over
-- statement:
--   The P construction uses the s5a4 primes over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1049-L1084
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1049-L1084

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
open UniqueFactorizationMonoid

theorem Formalism.HermitianLatticeCounting.P.s5a4_primes_over {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card ≤ finrank ℚ K ∧
      ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → Q ∈ s := by sorry
