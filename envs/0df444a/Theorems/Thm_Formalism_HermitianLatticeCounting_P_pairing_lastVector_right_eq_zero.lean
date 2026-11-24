-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_right_eq_zero
-- name    : Formalism.HermitianLatticeCounting.P.pairing_lastVector_right_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:33.94721+00:00
-- url     : https://prove2.me/theorems/f7d1f5f5-4774-4396-be6d-6ad441fdcf91
-- title:
--   P: pairing last Vector right eq zero
-- statement:
--   The P construction uses the pairing last Vector right eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L766-L771
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L766-L771

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

theorem Formalism.HermitianLatticeCounting.P.pairing_lastVector_right_eq_zero (F F' : FlagD H r) {c : K} (hz : F'.z - c • F.z ∈ F.X ⊔ F'.X) {v : V}
    (h1 : ∀ u ∈ F.X, H.B u v = 0) (h2 : ∀ u ∈ F'.X, H.B u v = 0) (h3 : H.B F.z v = 0) :
    H.B F'.z v = 0 := by sorry
