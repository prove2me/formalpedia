-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_eq_range
-- name    : Formalism.HermitianLatticeCounting.P.Xa_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:33.996672+00:00
-- url     : https://prove2.me/theorems/b9b1fd39-7ac3-4e2e-94ba-1969d0ba1a1a
-- title:
--   P: Xa eq range
-- statement:
--   The P construction uses the Xa eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L377-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L377-L387

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

theorem Formalism.HermitianLatticeCounting.P.Xa_eq_range (F : FlagD H r) {j : ℕ} (hj : j ≤ r) :
    F.Xa j = Submodule.span K
      (Set.range fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) := by sorry
