-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_sq_orthogonal_sum_le
-- name    : Formalism.HermitianLatticeCounting.P.norm_sq_orthogonal_sum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:32.3606+00:00
-- url     : https://prove2.me/theorems/07cd766e-8905-4318-a098-2c748148334e
-- title:
--   P: norm sq orthogonal sum le
-- statement:
--   The P construction uses the norm sq orthogonal sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L325-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L325-L344

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem Formalism.HermitianLatticeCounting.P.norm_sq_orthogonal_sum_le {j : ℕ} (h : Fin j → U) (horth : ∀ k l, k ≠ l → inner ℂ (h k) (h l) = 0)
    (h1 : ∀ k, ‖h k‖ ≤ 1) (c : Fin j → ℂ) : ‖∑ k, c k • h k‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 := by sorry
