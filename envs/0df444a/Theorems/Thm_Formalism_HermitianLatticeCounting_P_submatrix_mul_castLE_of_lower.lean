-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_submatrix_mul_castLE_of_lower
-- name    : Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:14.863172+00:00
-- url     : https://prove2.me/theorems/21d7f0be-384c-47c9-bdf9-d0f6e2696b3f
-- title:
--   P: submatrix mul cast LE of lower
-- statement:
--   The P construction uses the submatrix mul cast LE of lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L8-L22

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

theorem Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_lower {R : Type*} [CommRing R] {N l : ℕ} {α : Type*} (hl : l ≤ N)
    (Lo : Matrix (Fin N) (Fin N) R) (X : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hLo : ∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → Lo i j = 0) :
    (Lo * X).submatrix (Fin.castLE hl) g =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) g := by sorry
