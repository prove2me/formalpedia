-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
-- name    : Formalism.HermitianLatticeCounting.P.Dl_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:39:13.075195+00:00
-- url     : https://prove2.me/theorems/457bf36e-9a9f-41a0-bfc1-653362ed85f5
-- title:
--   P: Dl eq
-- statement:
--   The P construction uses the Dl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L683-L684
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L683-L684

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

theorem Formalism.HermitianLatticeCounting.P.Dl_eq (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) :
    Dl F F' l hl = (Matrix.of fun a b : Fin l => H.B (F.e (Fin.castLE hl a)) (F'.e (Fin.castLE hl b))).det := by sorry
