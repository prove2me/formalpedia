-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_unique
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_prime_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:27.865087+00:00
-- url     : https://prove2.me/theorems/4e52d744-0f08-4965-a1f4-c53729f7cbb4
-- title:
--   P: s5a4 prime unique
-- statement:
--   The P construction uses the s5a4 prime unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1035-L1046
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1035-L1046

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_prime_unique {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpQ : (p : 𝓞 K) ∈ Q) (hqQ : (q : 𝓞 K) ∈ Q) : p = q := by sorry
