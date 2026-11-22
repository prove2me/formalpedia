-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_sum_left
-- name    : Formalism.HermitianLatticeCounting.P.B_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:34.476632+00:00
-- url     : https://prove2.me/theorems/f90a841d-d518-48da-9f71-74d474a6ea46
-- title:
--   P: B sum left
-- statement:
--   The P construction uses the B sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L646-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L646-L650

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

theorem Formalism.HermitianLatticeCounting.P.B_sum_left (H : HermSpace K V) {n : ℕ} (c : Fin n → K) (u : Fin n → V) (y : V) :
    H.B (∑ a, c a • u a) y = ∑ a, c a * H.B (u a) y := by sorry
