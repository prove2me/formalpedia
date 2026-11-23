-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_eq_zero_of_mem_jointSpan
-- name    : Formalism.HermitianLatticeCounting.P.pairing_eq_zero_of_mem_jointSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:40.336163+00:00
-- url     : https://prove2.me/theorems/eea3a3d0-ebaa-4e1b-9790-be16d52dbab0
-- title:
--   P: pairing eq zero of mem joint Span
-- statement:
--   The P construction uses the pairing eq zero of mem joint Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L733-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L733-L744

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

theorem Formalism.HermitianLatticeCounting.P.pairing_eq_zero_of_mem_jointSpan (F F' : FlagD H r) {v : V} (h1 : ∀ u ∈ F.X, H.B u v = 0) (h2 : ∀ u ∈ F'.X, H.B u v = 0)
    (h3 : H.B F.z v = 0) (h4 : H.B F'.z v = 0) : ∀ u ∈ V0 F F', H.B u v = 0 := by sorry
