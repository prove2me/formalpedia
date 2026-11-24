-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_compl
-- name    : Formalism.HermitianLatticeCounting.P.finrank_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:06.51936+00:00
-- url     : https://prove2.me/theorems/81bbef23-1b7f-455d-abd0-f8bae0f1494e
-- title:
--   P: finrank compl
-- statement:
--   The P construction uses the finrank compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L403-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L403-L407

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

theorem Formalism.HermitianLatticeCounting.P.finrank_compl [FiniteDimensional K V] (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (I : Submodule K V)
    (h1 : F.X = F.Xa j ⊔ I) (h2 : I ⊓ F.Xa j = ⊥) : Module.finrank K I = r - j := by sorry
