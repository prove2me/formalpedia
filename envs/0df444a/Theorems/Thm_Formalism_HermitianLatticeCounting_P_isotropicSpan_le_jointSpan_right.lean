-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_right
-- name    : Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:45.879608+00:00
-- url     : https://prove2.me/theorems/670e9214-5f30-4c95-9f85-1fb30bff8b81
-- title:
--   P: isotropic Span le joint Span right
-- statement:
--   The P construction uses the isotropic Span le joint Span right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L749-L751
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L749-L751

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

theorem Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right (F F' : FlagD H r) : F'.X ≤ V0 F F' := by sorry
