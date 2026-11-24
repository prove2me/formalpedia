-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_level_lt_of_mem
-- name    : Formalism.HermitianLatticeCounting.P.level_lt_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:40.88514+00:00
-- url     : https://prove2.me/theorems/28fb024e-959b-491c-899c-a03f5a3f26dd
-- title:
--   P: level lt of mem
-- statement:
--   The P construction uses the level lt of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L170-L174

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

theorem Formalism.HermitianLatticeCounting.P.level_lt_of_mem (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) {n : ℕ}
    (hx : x ∈ F.Xa n) : a.val < n := by sorry
