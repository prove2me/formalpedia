-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_succ_eq_castSucc
-- name    : Formalism.HermitianLatticeCounting.P.succ_eq_castSucc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:26.524462+00:00
-- url     : https://prove2.me/theorems/96afa5f7-f1ed-46b8-b680-cb206a550b3e
-- title:
--   P: succ eq cast Succ
-- statement:
--   The P construction uses the succ eq cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L456-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L456-L457

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
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem Formalism.HermitianLatticeCounting.P.succ_eq_castSucc {r : ℕ} (a : Fin r) (h : a.val + 1 < r) :
    a.succ = (⟨a.val + 1, h⟩ : Fin r).castSucc := by sorry
