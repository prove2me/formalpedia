-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_jointSpan_eq
-- name    : Formalism.HermitianLatticeCounting.P.jointSpan_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:00.589995+00:00
-- url     : https://prove2.me/theorems/4420f255-0e05-4b3e-bbdc-06447cb49ec3
-- title:
--   P: joint Span eq
-- statement:
--   The P construction uses the joint Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L985-L997
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L985-L997

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

theorem Formalism.HermitianLatticeCounting.P.jointSpan_eq (F F' : FlagD H r) {c : K} (hz : F'.z - c • F.z ∈ F.X ⊔ F'.X) :
    V0 F F' = (F.X ⊔ F'.X) ⊔ K ∙ F.z := by sorry
