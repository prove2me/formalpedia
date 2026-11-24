-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_submatrix_mul_castLE_of_upper
-- name    : Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_upper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:20.285852+00:00
-- url     : https://prove2.me/theorems/e9727f65-2c1a-432b-a266-cacb43e45db1
-- title:
--   P: submatrix mul cast LE of upper
-- statement:
--   The P construction uses the submatrix mul cast LE of upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L24-L38

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

theorem Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_upper {R : Type*} [CommRing R] {N l : ℕ} {α : Type*} (hl : l ≤ N)
    (X : Matrix (Fin N) (Fin N) R) (Up : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hUp : ∀ i j : Fin N, l ≤ (i : ℕ) → (j : ℕ) < l → Up i j = 0) :
    (X * Up).submatrix g (Fin.castLE hl) =
      X.submatrix g (Fin.castLE hl) * Up.submatrix (Fin.castLE hl) (Fin.castLE hl) := by sorry
