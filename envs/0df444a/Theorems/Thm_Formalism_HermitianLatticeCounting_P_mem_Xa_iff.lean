-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_Xa_iff
-- name    : Formalism.HermitianLatticeCounting.P.mem_Xa_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:37.160007+00:00
-- url     : https://prove2.me/theorems/b6423100-70ad-4987-be36-5cbd6de7e3e5
-- title:
--   P: mem Xa iff
-- statement:
--   The P construction uses the mem Xa iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L399-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L399-L401

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
  {H : HermSpace K V} {r : ℕ}

theorem Formalism.HermitianLatticeCounting.P.mem_Xa_iff (F : FlagD H r) {j : ℕ} (hj : j ≤ r) {x : V} :
    x ∈ F.Xa j ↔ ∃ c : Fin j → K, ∑ a, c a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) = x := by sorry
