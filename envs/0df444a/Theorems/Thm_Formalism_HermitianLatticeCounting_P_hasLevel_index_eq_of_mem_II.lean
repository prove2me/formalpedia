-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_hasLevel_index_eq_of_mem_II
-- name    : Formalism.HermitianLatticeCounting.P.hasLevel_index_eq_of_mem_II
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:38.667968+00:00
-- url     : https://prove2.me/theorems/7b38318e-c122-4798-b425-abf98b8c58cf
-- title:
--   P: has Level index eq of mem II
-- statement:
--   The P construction uses the has Level index eq of mem II property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L461-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L461-L560

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem Formalism.HermitianLatticeCounting.P.hasLevel_index_eq_of_mem_II (F F' : FlagD H r) (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) (hμ : ∃ μ : K, μ + star μ ≠ 0) (hrel : Relevant F F') :
    ∀ (k : ℕ) (x : V) (a a' : Fin r) (al al' : K), a.val + 1 + k = r → x ∈ II F F' →
      F.HasLevel x a al → F'.HasLevel x a' al' →
      a = a' ∧ F'.z - (al / al') • F.z ∈ F.X ⊔ F'.X ∧
      ∀ b : Fin r, a.val ≤ b.val → ∃ y ∈ II F F', F.HasLevel y b al ∧ F'.HasLevel y b al' := by sorry
