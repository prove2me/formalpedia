-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_perpS
-- name    : Formalism.HermitianLatticeCounting.P.mem_perpS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:55.114658+00:00
-- url     : https://prove2.me/theorems/eb33baa4-00a8-4120-afd7-be1c19e1ee49
-- title:
--   P: mem perp S
-- statement:
--   The P construction uses the mem perp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1331-L1332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1331-L1332

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

theorem Formalism.HermitianLatticeCounting.P.mem_perpS (H : HermSpace K V) (S : Submodule K V) (v : V) :
    v ∈ perpS H S ↔ ∀ s ∈ S, H.B s v = 0 := by sorry
