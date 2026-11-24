-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove
-- name    : Formalism.HermitianLatticeCounting.P.det_submatrix_consRow_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:25.031549+00:00
-- url     : https://prove2.me/theorems/3e7b7c49-a535-4c69-85b2-dc377b37fc63
-- title:
--   P: det submatrix cons Row succ Above
-- statement:
--   The P construction uses the det submatrix cons Row succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L199-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L199-L217

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
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

theorem Formalism.HermitianLatticeCounting.P.det_submatrix_consRow_succAbove {R : Type*} [CommRing R] {n : ℕ} (Y : Matrix (Fin (n + 1)) (Fin (n + 2)) R)
    (u : Fin (n + 2) → R) (b₀ : Fin (n + 2)) (a : Fin (n + 1)) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by sorry
