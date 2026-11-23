-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_Xa
-- name    : Formalism.HermitianLatticeCounting.P.perp_Xa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:25.388795+00:00
-- url     : https://prove2.me/theorems/b63fdd9a-a3bd-45c9-a8c0-604c9bff4c1e
-- title:
--   P: perp Xa
-- statement:
--   The P construction uses the perp Xa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L61-L66

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

theorem Formalism.HermitianLatticeCounting.P.perp_Xa (F : FlagD H r) {a : ℕ} {v : V}
    (h : ∀ b : Fin r, b.val < a → H.B (F.e b.castSucc) v = 0) : ∀ u ∈ F.Xa a, H.B u v = 0 := by sorry
