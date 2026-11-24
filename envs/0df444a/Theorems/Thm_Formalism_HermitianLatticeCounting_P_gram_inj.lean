-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_inj
-- name    : Formalism.HermitianLatticeCounting.P.gram_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:24.07538+00:00
-- url     : https://prove2.me/theorems/e06c6bbd-b5b1-4d49-bfd5-d0ef92eff6ee
-- title:
--   P: gram inj
-- statement:
--   The P construction uses the gram inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L663-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L663-L673

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

theorem Formalism.HermitianLatticeCounting.P.gram_inj (H : HermSpace K V) {n : ℕ} (u w : Fin n → V)
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det ≠ 0) (c : Fin n → K)
    (h : ∀ b, H.B (∑ a, c a • u a) (w b) = 0) : c = 0 := by sorry
