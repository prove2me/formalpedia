-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_val
-- name    : Formalism.HermitianLatticeCounting.P.s5a4_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:31.638806+00:00
-- url     : https://prove2.me/theorems/8c473556-e8b6-44cb-ac90-c7fa6aa992d1
-- title:
--   P: s5a4 val
-- statement:
--   The P construction uses the s5a4 val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1114-L1147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegerGroupLocalParametrization.lean#L1114-L1147

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

theorem Formalism.HermitianLatticeCounting.P.s5a4_val {K : Type} [Field K] [NumberField K] (ι : Ideal (𝓞 K) → Fin (finrank ℚ K))
    (hι : ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q')
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 K) ∈ P)
    (hk : Ideal.absNorm P = p ^ k) (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) [DecidableEq (Ideal (𝓞 K))] :
    (((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod).factorization p =
      k * s.count P := by sorry
