-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp
-- name    : Formalism.HermitianLatticeCounting.P.GoodMap.comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:28.214561+00:00
-- url     : https://prove2.me/theorems/f673eeaf-3cf1-4d6c-bc06-f5afa5a6abb7
-- title:
--   Good Map: comp
-- statement:
--   The Good Map construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1514-L1536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1514-L1536

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

theorem Formalism.HermitianLatticeCounting.P.GoodMap.comp (F F' : FlagD H r) {g g' : V →ₗ[K] V} (hg : GoodMap F F' g) (hg' : GoodMap F F' g') :
    GoodMap F F' (g ∘ₗ g') := by sorry
